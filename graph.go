package gorgonia

import (
	"bytes"
	"fmt"

	"github.com/awalterschulze/gographviz"
	"gonum.org/v1/gonum/graph"
)

// ExprGraph is a data structure for a directed acyclic graph (of expressions). This structure is the main entry point
// for Gorgonia.
type ExprGraph struct {
	name string

	// all is the lookup table for all nodes. It's the only thing that the GC needs to scan
	all Nodes

	byHash map[uint32]NodeID
	evac   map[uint32]NodeIDs
	to     map[NodeID]NodeIDs

	leaves    NodeIDs
	constants NodeIDs
	roots     NodeIDs
	counter   uint
}

type graphconopt func(g *ExprGraph)

// WithGraphName is a ExprGraph construction option that provides a name.
func WithGraphName(name string) graphconopt {
	f := func(g *ExprGraph) {
		g.name = name
	}
	return f
}

// NewGraph creates a new graph. Duh
func NewGraph(opts ...graphconopt) *ExprGraph {
	g := &ExprGraph{
		byHash: make(map[uint32]NodeID),
		evac:   make(map[uint32]NodeIDs),
		to:     make(map[NodeID]NodeIDs),

		leaves:    make(NodeIDs, 0, 64),
		constants: make(NodeIDs, 0, 8),
	}

	for _, opt := range opts {
		opt(g)
	}

	return g
}

// Clone clones the graph. All nodes gets cloned, and their values are cloned as well.
func (g *ExprGraph) Clone() interface{} {
	g2 := new(ExprGraph)
	g2.name = g.name

	mapping := make(map[*Node]*Node) // a map of old nodes to new nodes
	g2.all = make(Nodes, len(g.all))
	for i, n := range g.all {
		cloned := n.Clone().(*Node)
		cloned.g = g2
		cloned.id = n.id

		g2.all[i] = cloned
		mapping[n] = cloned
	}

	// handle each node's children, deriv ofs, etc
	for i, n := range g.all {
		cloned := g2.all[i]
		cloned.children = make(NodeIDs, len(n.children))
		for j, cid := range n.children {
			c := g.Node(cid)
			cloned.children[j] = mapping[c].id
		}

		cloned.derivOf = make(NodeIDs, len(n.derivOf))
		for j, cid := range n.derivOf {
			c := g.Node(cid)
			cloned.derivOf[j] = mapping[c].id
		}

		if n.deriv != -1 {
			deriv := g.Node(n.deriv)
			cloned.deriv = mapping[deriv].id
		}
	}

	g2.byHash = make(map[uint32]NodeID)
	for k, vid := range g.byHash {
		v := g.Node(vid)
		g2.byHash[k] = mapping[v].id
	}

	g2.evac = make(map[uint32]NodeIDs)
	for k, v := range g.evac {
		g2.evac[k] = make(NodeIDs, len(v))
		for i, nid := range v {
			n := g.Node(nid)
			g2.evac[k][i] = mapping[n].id
		}
	}

	g2.to = make(map[NodeID]NodeIDs)
	for kid, v := range g.to {
		k := g.Node(kid)
		to := mapping[k]
		g2.to[to.id] = make(NodeIDs, len(v))
		for i, nid := range v {
			n := g.Node(nid)
			g2.to[to.id][i] = mapping[n].id
		}
	}

	g2.leaves = make(NodeIDs, len(g.leaves))
	for i, nid := range g.leaves {
		n := g.Node(nid)
		g2.leaves[i] = mapping[n].id
	}

	g2.constants = make(NodeIDs, len(g.constants))
	for i, nid := range g.constants {
		n := g.Node(nid)
		g2.constants[i] = mapping[n].id
	}

	g2.roots = make(NodeIDs, len(g.roots))
	for i, nid := range g.roots {
		n := g.Node(nid)
		g2.roots[i] = mapping[n].id
	}

	g2.counter = g.counter
	return g2
}

// AddNode adds n to the graph. It panics if the added node ID matches an existing node ID.
func (g *ExprGraph) AddNode(n *Node) (retVal *Node) {
	defer func() {
		if _, ok := g.to[retVal.id]; !ok {
			g.to[retVal.id] = nil
		}
	}()

	hash := n.Hashcode()
	if existing, ok := g.byHash[hash]; ok {
		if existing < 0 {
			// this means that there has been previous collisions
			// so look at evac map
			for _, eid := range g.evac[hash] {
				e := g.Node(eid)
				if nodeEq(n, e) {
					return e
				}
			}
			g.evac[hash] = append(g.evac[hash], n.id)
			g.addToAll(n)
			incrCC() // collision counter
			return n
		}
		existingNode := g.Node(existing)
		if !nodeEq(n, existingNode) {
			g.evac[hash] = NodeIDs{existing, n.id}
			g.byHash[hash] = -1 // to signal that it's collided
			g.addToAll(n)
			incrCC()
			return n
		}
		incrEC() // expected collision (they're the same node!)
		return existingNode
	}

	if n.isConstant() {
		n = n.clone()
		n.g = g
	}

	g.addToAll(n)
	g.byHash[hash] = n.id
	if n.isConstant() {
		g.constants = g.constants.Add(n.id)
	}
	return n
}

func (g *ExprGraph) addToAll(n *Node) {
	if n == nil {
		panic("HELP! trying to add nil")
	}
	g.all = append(g.all, n)
	n.id = NodeID(g.counter)
	g.counter++
}

// RemoveNode removes n from the graph, as well as any edges attached to it. If the node
// is not in the graph it is a no-op.
func (g *ExprGraph) RemoveNode(node graph.Node) {
	n := node.(*Node)
	if n.id == -1 {
		return // if it's -1, it was never in the graph to begin with
	}

	hash := n.Hashcode()

	delete(g.byHash, hash)
	delete(g.to, n.id)
	g.evac[hash] = g.evac[hash].remove(n.id)
	g.all = g.all.remove(n)
}

// SetEdge adds e, an edge from one node to another. If the nodes do not exist, they are added.
// It will panic if the IDs of the e.From and e.To are equal.
func (g *ExprGraph) SetEdge(e graph.Edge) {
	from := e.From().(*Node)
	to := e.To().(*Node)

	if from == to {
		panic(fmt.Sprintf("cannot add self edge: from %v to %v", from, to))
	}

	if !g.Has(from) {
		from = g.AddNode(from)
	}

	if !g.Has(to) {
		to = g.AddNode(to)
	}

	// g.to[to] = g.to[to].Add(from)
	g.to[to.id] = append(g.to[to.id], from.id)
}

// Roots returns a list of nodes that are not children of any other nodes
func (g *ExprGraph) Roots() (retVal Nodes) {
	// handle subgraph
	if g.roots != nil {
		return g.NodesFromNodeIDs(g.roots)
	}

	for nid, tos := range g.to {
		n := g.Node(nid)
		if len(tos) == 0 {
			retVal = append(retVal, n)
		}
		// if the root is a statement (typically a read), and it only has one child
		if len(n.children) == 1 && n.isStmt {
			childID := n.children[0]
			if len(g.to[childID]) == 1 {
				retVal = append(retVal, g.Node(childID))
			}
		}
	}

	g.roots = make(NodeIDs, len(retVal))
	for i, n := range retVal {
		g.roots[i] = n.id
	}
	return retVal
}

// Inputs returns a list of nodes which are inputs (that is to say, the user is required to set a value in it)
func (g *ExprGraph) Inputs() (retVal Nodes) {
	for _, n := range g.all {
		if n.isInput() {
			retVal = append(retVal, n)
		}
	}
	return
}

// UnbindAll unbinds all the values from the nodes
func (g *ExprGraph) UnbindAll() {
	for _, n := range g.all {
		n.unbind()
	}
}

// UnbindAllNonInputs unbinds all the values from nodes that aren't input nodes
func (g *ExprGraph) UnbindAllNonInputs() {
	for _, n := range g.all {
		if n.isInput() {
			continue
		}
		n.unbind()
	}
}

// ByName returns nodes that have the name provided.
// Bear in mind that the name that is compared to is the internal name,
// not the result of calling node.Name(). The reason for doing this is
// for ease of finding only names that are user-supplied, instead of autogenerated names
func (g *ExprGraph) ByName(name string) (retVal Nodes) {
	for _, n := range g.all {
		if n.name == name {
			retVal = append(retVal, n)
		}
	}
	return
}

// Constant returns a constant that may be found in the graph. If no constant were found, a new one is created instead
func (g *ExprGraph) Constant(v Value) *Node {
	for _, nid := range g.constants {
		n := g.Node(nid)
		if ValueEq(n.Value(), v) {
			return n
		}
	}

	n := NewConstant(v)
	return g.AddNode(n)
}

func (g *ExprGraph) String() string {
	var buf bytes.Buffer
	buf.WriteString("Graph: [\n")
	for _, nid := range g.byHash {
		n := g.Node(nid)
		fmt.Fprintf(&buf, "\t%d: %s\n", n.Hashcode(), n)
	}
	buf.WriteString("]")
	return buf.String()
}

// ToDot generates the graph in graphviz format. The use of this is to generate for the entire graph
// which may have multiple trees with different roots
// TODO: This is getting unwieldy. Perhaps refactor out into a ToDot(...Opt)?
func (g *ExprGraph) ToDot() string {
	gv := gographviz.NewEscape()
	gv.SetName(fullGraphName)
	gv.SetDir(true)

	gv.AddAttr(fullGraphName, "nodesep", "1")
	gv.AddAttr(fullGraphName, "ranksep", "1.5 equally")
	gv.AddAttr(fullGraphName, "rankdir", "TB")
	if len(g.byHash) > 100 {
		gv.AddAttr(fullGraphName, "nslimit", "3") // numiter=3*len(nodes)
		// gv.AddAttr(fullGraphName, "splines", "line") // ugly as sin.
	}

	groups := make(map[string]struct{})
	for h, nid := range g.byHash {
		n := g.Node(nid)
		if nid >= 0 {
			group := n.dotCluster()
			groups[group] = struct{}{}
			continue
		}
		// other wise it'se a clash of hash
		for _, nid2 := range g.evac[h] {
			n := g.Node(nid2)
			group := n.dotCluster()
			groups[group] = struct{}{}

		}
	}

	for grp := range groups {
		attrs := map[string]string{"label": grp}

		parentGraph := fullGraphName
		if grp == inputsClust || grp == constantsClust {
			parentGraph = inputConsts
			if !gv.IsSubGraph(inputConsts) {
				groupAttrs := map[string]string{"rank": "max"}
				gv.AddSubGraph(fullGraphName, inputConsts, groupAttrs)
			}
		}
		gv.AddSubGraph(parentGraph, "cluster_"+grp, attrs)
	}

	// for _, n := range g.byHash {
	for _, n := range g.all {
		group := n.dotCluster()
		n.dotString(gv, "cluster_"+group)
	}

	// for _, from := range g.byHash {
	for _, from := range g.all {
		for i, childID := range from.children {
			child := g.Node(childID)
			if ok := g.all.Contains(child); !ok {
				// not in graph, so ignore it...
				continue
			}
			fromID := fmt.Sprintf("Node_%p", from)
			toID := fmt.Sprintf("Node_%p", child)

			edgeAttrs := map[string]string{
				"taillabel":  fmt.Sprintf(" %d ", i),
				"labelfloat": "false",
			}

			// we invert the from and to nodes for gradients, As the expressionGraph builds upwards from bottom, the gradient builds downwards.
			if from.group == gradClust && child.group == gradClust {
				edgeAttrs["dir"] = "back"
				gv.AddPortEdge(toID, toID+":anchor:s", fromID, fromID+":anchor:n", true, edgeAttrs)
			} else {
				gv.AddPortEdge(fromID, fromID+":anchor:s", toID, toID+":anchor:n", true, edgeAttrs)
			}
		}
	}

	// draw deriv lines
	if debugDerives {
		edgeAttrs := map[string]string{
			"style":      "dashed",
			"constraint": "false",
			"weight":     "999",
		}

		for _, nid := range g.byHash {
			n := g.Node(nid)
			if nid < 0 {
				// collision found... what to do?
				continue
			}
			if n.derivOf != nil {
				id := fmt.Sprintf("Node_%p", n)
				for _, derivOfID := range n.derivOf {
					derivOf := g.Node(derivOfID)
					if _, ok := g.to[derivOfID]; !ok {
						continue
					}
					ofID := fmt.Sprintf("Node_%p", derivOf)
					// gv.AddPortEdge(id, ":anchor:w", ofID, ofID+":anchor:e", true, edgeAttrs)
					gv.AddEdge(id, ofID, true, edgeAttrs)
				}
			}
		}
	}

	// stupid invisible nodes to keep expressiongraph on the left
	subGAttrs := make(map[string]string)
	// subGAttrs.Add("rank", "max")
	gv.AddSubGraph(fullGraphName, outsideSubG, subGAttrs)

	attrs := map[string]string{
		"style": "invis",
	}
	gv.AddNode(outsideSubG, outsideRoot, attrs)

	outsides := []string{outsideRoot}
	var insides []string

	// build the inside and outside list
	if _, hasInputs := groups[inputsClust]; hasInputs {
		insides = append(insides, insideInputs)
		gv.AddNode("cluster_inputs", insideInputs, attrs)
	}

	if _, hasConst := groups[constantsClust]; hasConst {
		if len(insides) > 0 {
			outsides = append(outsides, outsideConsts)
			gv.AddNode(outsideSubG, outsideConsts, attrs)
		}
		insides = append(insides, insideConsts)
		gv.AddNode("cluster_constants", insideConsts, attrs)
	}

	if len(insides) > 0 {
		outsides = append(outsides, outsideExprG)
		gv.AddNode(outsideSubG, outsideExprG, attrs)
	}
	insides = append(insides, insideExprG)
	gv.AddNode("cluster_expressionGraph", insideExprG, attrs)

	for group := range groups {
		if group == exprgraphClust || group == constantsClust || group == inputsClust {
			continue
		}
		inside := "inside_" + group
		outside := "outside_" + group
		insides = append(insides, inside)
		outsides = append(outsides, outside)

		gv.AddNode(outsideSubG, outside, attrs)
		gv.AddNode("cluster_"+group, inside, attrs)
	}

	edgeAttrs := map[string]string{
		"style":      "invis",
		"weight":     "999",
		"constraint": "false",
	}
	for i, o := range outsides {
		// outside-inside
		gv.AddEdge(o, insides[i], true, edgeAttrs)

		if i > 0 {
			// outside-outside
			gv.AddEdge(outsides[i-1], o, true, edgeAttrs)

			// inside-inside
			gv.AddEdge(insides[i-1], insides[i], true, edgeAttrs)
		}
	}
	return gv.String()
}

// other private methods

func (g *ExprGraph) removeAllEdgesFrom(n *Node) {
	for k, ns := range g.to {
		g.to[k] = ns.remove(n.id)
	}
}

/* Graph interface */

// Node returns the node in the graph with the given ID.
func (g *ExprGraph) Node(id NodeID) *Node {
	if int(id) >= len(g.all) || id < 0 {
		return nil
	}
	return g.all[int(id)]
}

// Has returns whether the node exists within the graph.
func (g *ExprGraph) Has(node graph.Node) bool {
	n := node.(*Node)
	_, ok := g.to[n.id]
	return ok
}

// Nodes returns all the nodes in the graph.
func (g *ExprGraph) Nodes() []graph.Node {
	// nodes := make([]graph.Node, len(g.from))
	ns := g.AllNodes()

	nodes := nodeToGraphNode(ns)
	return nodes
}

// AllNodes is like Nodes, but returns Nodes instead of []graph.Node.
// Nodes() has been reserved for the graph.Directed interface, so this one is named AllNodes instead
func (g *ExprGraph) AllNodes() Nodes {
	return g.all
}

func (g *ExprGraph) NodesFromNodeIDs(ids NodeIDs) Nodes {
	retVal := make(Nodes, len(ids))
	for i, id := range ids {
		retVal[i] = g.Node(id)
	}
	return retVal
}

// From returns all nodes in g that can be reached directly from n.
func (g *ExprGraph) From(node graph.Node) []graph.Node {
	n := node.(*Node)
	return nodeToGraphNode(g.NodesFromNodeIDs(n.children))
}

// HasEdgeBetween returns whether an edge exists between nodes x and y without
// considering direction.
func (g *ExprGraph) HasEdgeBetween(x, y graph.Node) bool {
	xid := x.(*Node)
	yid := y.(*Node)

	return xid.children.Contains(yid.id) || yid.children.Contains(xid.id)
}

// Edge returns the edge from u to v if such an edge exists and nil otherwise.
// The node v must be directly reachable from u as defined by the From method.
func (g *ExprGraph) Edge(u, v graph.Node) graph.Edge {
	uid := u.(*Node)
	vid := v.(*Node)

	if !uid.children.Contains(vid.id) {
		return nil
	}
	e := edge{from: uid, to: vid}
	return e
}

/* Directed interface */

// HasEdgeFromTo returns whether an edge exists in the graph from u to v.
func (g *ExprGraph) HasEdgeFromTo(u, v graph.Node) bool {
	uid := u.(*Node)
	vid := v.(*Node)

	return uid.children.Contains(vid.id)
}

// To returns all nodes in g that can reach directly to n.
func (g *ExprGraph) To(n graph.Node) []graph.Node {
	nodeIDs := g.to[n.(*Node).id]
	ns := g.NodesFromNodeIDs(nodeIDs).Set()
	g.to[n.(*Node).id] = nodeIDs
	return nodeToGraphNode(ns)
}

// subgraph is basically a subset of nodes. This is useful for compiling sub sections of the graph
func (g *ExprGraph) subgraph(ns Nodes, opts ...Nodes) *ExprGraph {
	// ns = ns.Set()

	var roots Nodes

	// add missing stuff first
	for _, n := range ns {
		for _, parent := range g.to[n] {
			if parent.isStmt {
				roots = append(roots, parent)
				ns = append(ns, parent)
			}
		}
	}

	// uniquify the froms and at the same time build a new roots
	allset := ns.mapSet()
	if len(opts) == 0 {
		for _, n := range ns {
			if len(g.to[n]) == 0 {
				if n.isStmt {
					roots = append(roots, n.children[0])
				} else {
					roots = append(roots, n)
				}
				continue
			}

			var hasParent bool
			for _, parent := range g.to[n] {
				if allset.Contains(parent) {
					hasParent = true
					break
				}
			}
			if !hasParent {
				roots = append(roots, n)
			}
		}
	} else {
		rs := opts[0]
		roots = make(Nodes, len(rs))
		for i, n := range rs {
			if n.isStmt {
				roots[i] = n.children[0]
				continue
			}
			roots[i] = n

		}
	}
	var leaves Nodes
	for _, n := range ns {
		if len(n.children) == 0 {
			leaves = append(leaves, n)
		}
	}

	// uniquify all the things
	roots = roots.Set()
	leaves = leaves.Set()
	ns = ns.Set()

	retVal := &ExprGraph{
		all:    ns,
		byHash: g.byHash,
		evac:   g.evac,
		to:     g.to,

		leaves:    leaves,
		constants: g.constants,
		roots:     roots,
	}

	return retVal
}

// Subgraph subsets a graph. This function has overloaded meanings - If only one node is passed in, it assumes that the one node is the root,
// otherwise, it treats ns as the subset of nodes to be included in the subgraph
func (g *ExprGraph) Subgraph(ns ...*Node) *ExprGraph {
	if len(ns) == 1 {
		g.SubgraphRoots(ns[0])
	}
	return g.subgraph(ns)
}

// SubgraphRoots creates a subgraph, assuming the provided nodes are roots to the new subgraph.
func (g *ExprGraph) SubgraphRoots(ns ...*Node) *ExprGraph {
	sub := make(Nodes, len(ns))
	copy(sub, ns)

	walked := NewNodeSet()
	for _, n := range ns {
		ch := make(chan *Node)
		go func(ch chan *Node) {
			defer close(ch)
			walkGraph(n, ch, walked)
		}(ch)

		for node := range ch {
			sub = append(sub, node)
		}
	}
	return g.subgraph(sub, ns)
}

type edge struct {
	from, to graph.Node
	weight   float64
}

func (e edge) From() graph.Node { return e.from }
func (e edge) To() graph.Node   { return e.to }
func (e edge) Weight() float64  { return e.weight }
