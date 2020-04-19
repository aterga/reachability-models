one sig HeapGraph {
	Ns: some N,
	adj: Ns set -> set Ns, 
	adjTC: Ns set -> set Ns
} {
	-- Transitive closure
	all n, m: Ns | (n->m) in adjTC iff m in n.*adj

	-- Weakly connected
	some root: N | Ns = root.*adj
}

some sig Graph {
	Ns: some N,
 	adj: Ns set -> set N,
	adjTC: Ns set -> set N
} {
	-- Local edges
	all n, m: N | (n->m) in adj iff (n->m) in HeapGraph.@adj and n in Ns
	
	-- Local paths
	all n, m: Ns | (n->m) in adjTC iff m in n.*adj
	all n, m: N | (n->m) in adjTC implies (n->m) in HeapGraph.@adjTC
}

sig N {
	succs: set N, 
	preds: set N
} {
	-- All Ns are in the heap graph
	some h: HeapGraph | this in h.Ns

	-- Successors
	succs = this.(HeapGraph.adj)

	-- Predecessors
	preds = (HeapGraph.adj).this
}

pred E[ctx: Graph, x: N, y: N] {
	(x in ctx.Ns) and (x->y) in ctx.adj
}

pred P[ctx: Graph, x: N, y: N] {
	(x = y) or ( (x->y) in ctx.adjTC )
}

fun sub[ctx: Graph, root: N]: some N {
	{ n: N | P[ctx, root, n] and n in ctx.Ns }
}

one sig g in Graph {}
one sig g1 in Graph {}
one sig r in N {}
one sig a in N {}

fact {
	#Graph = 2
	r in g.Ns
	g1.Ns = sub[g, r]
	--some n: N | n in g.Ns and n not in g1.Ns 
	
	P[g, r, a]
	a not in g.Ns
}

assert subAlwaysYieldsSubset {
	all ctx: Graph, root: N | root in ctx.Ns implies sub[ctx, root] in ctx.Ns
}

assert SmokeTest { {} }

--check SmokeTest for 10 N, 2 Graph
--check subAlwaysYieldsSubset for 20 N, 2 Graph
run {} for 10 N, 2 Graph
