# Spathoulas Dimitris

import heapq
from typing import List, Dict, Set, Tuple

Vertex = int
Length = float

def base_case_bmssp(
    B: Length,
    S: Set[Vertex],
    adj: Dict[Vertex, List[Tuple[Vertex, Length]]],
    k: int
) -> Tuple[Length, Set[Vertex]]:
    """
    Base case for BMSSP, Algorithm 2.

    Args:
        B: upper bound distance threshold
        S: singleton set {x}, where x is complete
        adj: adjacency list {u: [(v, weight), ...]}
        k: integer threshold for pivot size

    Returns:
        (B_prime, U)
        - B_prime: new boundary (<= B)
        - U: set of vertices found
    """
    assert len(S) == 1, "S must be a singleton {x}"
    x = next(iter(S))

    # Initialize distances
    bd = {v: float('inf') for v in adj}
    bd[x] = 0

    # Min-heap of (distance, vertex)
    heap = [(0.0, x)]
    U0 = set()

    while heap and len(U0) < k + 1:
        dist_u, u = heapq.heappop(heap)
        if u in U0:
            continue  # Skip if already processed
        U0.add(u)

        for v, w_uv in adj.get(u, []):
            new_dist = dist_u + w_uv
            if new_dist < bd[v] and new_dist < B:
                bd[v] = new_dist
                heapq.heappush(heap, (new_dist, v))

    # Decide output based on number of vertices found
    if len(U0) <= k:
        return B, U0
    else:
        B_prime = max(bd[v] for v in U0)
        U = {v for v in U0 if bd[v] < B_prime}
        return B_prime, U
