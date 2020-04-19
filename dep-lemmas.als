one sig Graph {
	Ns: some N,
	adj: N set -> set N, 
	adjTC: N set -> set N, 
	DEP: N set -> set N -> set N -> set N, 
} {
	all n, m: N | (n->m) in adjTC iff m in n.*adj 

	-- weakly connected
	some root: N | Ns = root.*adj  
}

sig N {
	succs: set N, 
	preds: set N
} {
	-- All Ns are in some graph
	some graph: Graph | this in graph.Ns 

	-- Successors 
	succs = this.(Graph.adj)

	-- Predecessors
	preds = (Graph.adj).this
}

fun SCC[from: set N]: set N {
	from.*(Graph.adj) & from.*~(Graph.adj)
}

fun inEdges[n: N]: (N set -> one N) {
	{ i: N | i in n.~(Graph.adj) } -> n
}

fun outEdges[n: N]: (N one -> set N) {
	n -> { o: N | o in n.(Graph.adj) }
}

fact AllSCCsAreSimple { 
	all n: N | all disj p, s: SCC[n] | 
		(not s in p.*(Graph.adj - inEdges[n] - outEdges[n])) or 
		(not p in s.*(Graph.adj - inEdges[n] - outEdges[n]))
}

fun Hammock[source, sink: N]: set N {
	{ n: N | n in source.*(Graph.adj) and n in sink.*~(Graph.adj) }
}

pred IsMinimalHammock[p, s: N] {
	#outEdges[p] > 1 
	#inEdges[s] > 1
	SCC[p] != SCC[s] 
}

fact AllHammocksAreAcyclic {
	all disj p, s: N | all n: Hammock[p, s] | 
		IsMinimalHammock[p, s] implies #SCC[n] = 1
}

fact NoHammocks { 
	all disj p, s: N | all n: Hammock[p, s] | 	
		IsMinimalHammock[p, s]
			implies 
				(not s in p.*(Graph.adj - inEdges[n] - outEdges[n]))
}

pred E[v1:N, v2:N] {
	(v1->v2) in Graph.adj 
}

pred P[v1:N, v2:N] {
	(v1->v2) in Graph.adjTC 
}

pred DEP(v1:N, v2:N, u1:N, u2:N) {
	(v1->v2->u1->u2) in Graph.DEP 
}

fun path[start:N, end:N]: set N {
	{ n: N | n in start.*(Graph.adj) and n in end.*^((Graph.adj)) }
}

pred EdgeSupportsPath[v1, v2, u1, u2: N]  {
	E[u1, u2] and u1 != u2
	P[v1, v2]
	P[v1, u1] and P[u2, v2]
	not v2 in ( v1.*(Graph.adj - (u1->u2)) )
}

fact DEP_Semantics {
	all v1, v2, u1, u2: N | DEP[v1, v2, u1, u2] iff EdgeSupportsPath[v1, v2, u1, u2]
}

assert ax_DEP_0_2 {
	all x, y: N | 
		E[x, y] and x != y iff DEP[x, y, x, y]
}

/**
	Found bug: (x != y) was missing! 
*/
assert ax_HeadTriangleImposable_BUG {
	all x, y, v: N |
		                E[x, v] and x != v and P[v, y] implies DEP[x, y, x, v]
}

assert ax_HeadTriangleImposable_FIX_GS {
	all x, y, v: N |
		!P[v, x] and
		/*x != y and*/ x != v and E[x, v] and P[v, y] implies DEP[x, y, x, v]
}

assert ax_HeadTriangleImposable_FIX_ATG {
	all x, y, v: N |
		(!P[v, x] or (all beta: x.succs | !DEP[v, y, x, beta])) and
		x != y and x != v and E[x, v] and P[v, y] implies DEP[x, y, x, v]
}

assert ax_TailTriangleImposable_BUG {
	all x, y, u: N | 
		P[x, u] and E[u, y] and u != y implies DEP[x, y, u, y] 
}

assert ax_TailTriangleImposable_FIX_GS {
	all x, y, u: N | 
		!P[y, u] and 
		/*x != y and*/ u != y and P[x, u] and E[u, y] implies DEP[x, y, u, y] 
}

assert ax_TailTriangleImposable_FIX_ATG {
	all x, y, u: N | 
		(!P[y, u] or (all beta: y.succs | !DEP[x, u, y, beta])) and
		x != y and u != y and P[x, u] and E[u, y] implies DEP[x, y, u, y] 
}


/**
	Weakened the LHS by adding (x = y)
*/
assert ax_NoEdgeNoDEP {
	all x, y, u, v: N |
		!E[u, v] || u = v || x = y implies !DEP[x,y,u,v] 
}

assert ax_DEP_6_head {
	all x, y, n: N |
		n != y implies !DEP[y, n, x, y]
}

assert ax_DEP_6_tail {
	all x, y, n: N |
		n != y implies !DEP[n, x, x, y]
}

assert ax_DEP_7 {
	all nu, n, mu, sigma: N | 
		nu != n && n != sigma && nu != mu && E[nu, sigma] && E[mu, sigma]
			implies not DEP[nu, n, mu, sigma] or mu = sigma
}

assert ax_DepNeedsCoalignedPathAndEdge { 
	all x, y, u, v: N | 
		!P[x, u] || !P[v, y] implies !DEP[x, y, u, v]
}

assert ax_TcToDep {
	all x, y: N | 
		P[x, y] && x != y => 
			some disj u, v: N | E[u, v] && DEP[x, y, u, v]
}

assert ax_DepToTc {
	all x, y, u, v: N | 
		DEP[x,y,u,v] =>
			P[x,y] && E[u,v] && u != v
}

assert ax_DefinitionOfDep {
	all x, y: N | 
		P[x, y] && x != y <=> 
			some u, v: N | DEP[x, y, u, v]
}

assert ax_TrivialPaths {
	all x: N | P[x,x] && all u, v: N | !DEP[x,x,u,v]
}

check ax_TrivialPaths for 10 
check ax_TcToDep for 10 but 7 N 
check ax_DepToTc for 10 but 7 N 
check ax_DefinitionOfDep for 10 but 7 N

check ax_DEP_0_2 for 10 but 7 N
check ax_HeadTriangleImposable_BUG for 10 but exactly 3 N
check ax_HeadTriangleImposable_FIX_GS for 10 but 7 N
check ax_HeadTriangleImposable_FIX_ATG for 10 but 7 N
check ax_TailTriangleImposable_BUG for 10 but exactly 3 N
check ax_TailTriangleImposable_FIX_GS  for 10 but 7 N
check ax_TailTriangleImposable_FIX_ATG  for 10 but 7 N
check ax_NoEdgeNoDEP for 10 but 7 N
check ax_DEP_6_head for 10 but 7 N
check ax_DEP_6_tail for 10 but 7 N
check ax_DEP_7 for 10 but 7 N
check ax_DepNeedsCoalignedPathAndEdge for 10 but 7 N

pred SomeLoops {
	some n: N | #SCC[n] = 2
	no n: N | n in n.(Graph.adj)
	some n: N | #inEdges[n] = 0
}


--run SomeLoops for 10 but exactly 3 N


--run {} for 10 but 5 N
