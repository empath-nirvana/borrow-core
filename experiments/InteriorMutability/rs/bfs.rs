// Breadth-first search over a shared graph whose nodes carry `visited: Cell<bool>` and
// `dist: Cell<i32>`, so the traversal needs only `&Graph` (winapi's build.rs marks its header
// graph the same way). Six nodes, edges 0-1, 0-2, 1-3, 2-3, 3-4; node 5 is unreachable.
// Prints (3, 5, 7): the distance to 4, the nodes reached, and the sum of their distances.
use std::cell::Cell;
use std::collections::VecDeque;

struct Node {
    edges: Vec<usize>,
    visited: Cell<bool>,
    dist: Cell<i32>,
}

struct Graph {
    nodes: Vec<Node>,
}

fn bfs(g: &Graph, start: usize) {
    let mut q = VecDeque::new();
    g.nodes[start].visited.set(true);
    q.push_back(start);
    while let Some(u) = q.pop_front() {
        for &v in &g.nodes[u].edges {
            if !g.nodes[v].visited.get() {
                g.nodes[v].visited.set(true);
                g.nodes[v].dist.set(g.nodes[u].dist.get() + 1);
                q.push_back(v);
            }
        }
    }
}

fn main() {
    let mut adj = vec![vec![]; 6];
    for (a, b) in [(0, 1), (0, 2), (1, 3), (2, 3), (3, 4)] {
        adj[a].push(b);
        adj[b].push(a);
    }
    let g = Graph {
        nodes: adj.into_iter().map(|edges| Node { edges, visited: Cell::new(false), dist: Cell::new(0) }).collect(),
    };
    bfs(&g, 0);
    let reached: Vec<&Node> = g.nodes.iter().filter(|n| n.visited.get()).collect();
    let sum: i32 = reached.iter().map(|n| n.dist.get()).sum();
    println!("({}, {}, {})", g.nodes[4].dist.get(), reached.len(), sum);
}
