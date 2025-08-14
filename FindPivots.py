# Spathoulas Dimitris

from lemma33 import Lemma33

class Graph:
    def __init__(self):
        # adjacency: node -> list of (neighbor, weight)
        self.adj = defaultdict(list)
        self.nodes = set()

    def add_edge(self, u, v, w=1):
        self.adj[u].append((v, w))
        self.nodes.add(u)
        self.nodes.add(v)

    def edges_from(self, u):
        return self.adj.get(u, [])


def find_pivots(graph, bd, S, B, k):
    """
     Algorithm 1: FindPivots(B, S).
    - graph: Graph object
    - bd: dict of distances (mutated by the function)
    - S: iterable of starting complete vertices
    - B: numeric bound
    - k: integer parameter

    Returns (P, W, bd, pred)
    - P: set of pivots (subset of S)
    - W: set of vertices encountered
    - bd: updated distances (same dict object)
    - pred: predecessor map used for tie-breaking (node -> parent node)
    """
    S = set(S)
    W = set(S)
    W_prev = set(S)
    pred = {}  # Pred[v] = parent u chosen when relaxing edge (u->v)

    # Relax for k steps
    for i in range(1, k+1):
        W_i = set()
        for u in list(W_prev):
            for v, w in graph.edges_from(u):
                newd = bd.get(u, float('inf')) + w
                if newd <= bd.get(v, float('inf')):
                    bd[v] = newd
                    pred[v] = u
                    if newd < B:
                        W_i.add(v)
        W.update(W_i)
        W_prev = W_i
        if len(W) > k * len(S):
            return set(S), W, bd, pred

    # Build F: edges (u,v) with u,v in W and bd[v] = bd[u] + w
    F_adj = defaultdict(list)
    F_incoming = defaultdict(int)
    for u in W:
        for v, w in graph.edges_from(u):
            if v in W:
                if abs(bd.get(v, float('inf')) - (bd.get(u, float('inf')) + w)) < 1e-12:
                    F_adj[u].append(v)
                    F_incoming[v] += 1

    # Roots among S in F
    roots = [u for u in S if F_incoming.get(u, 0) == 0 and u in W]

    # Find pivots
    P = set()
    visited_global = set()
    for r in roots:
        if r in visited_global:
            continue
        stack = [r]
        comp_nodes = set()
        while stack:
            x = stack.pop()
            if x in comp_nodes:
                continue
            comp_nodes.add(x)
            for y in F_adj.get(x, ()):
                if y not in comp_nodes:
                    stack.append(y)
        visited_global.update(comp_nodes)
        if len(comp_nodes) >= k:
            P.add(r)

    return P, W, bd, pred
