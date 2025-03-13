## Graph / Verticies / Edges
Graph G = (V, E), where V and E are sets of vertices and edges respectivly.  
An edge is a set of conections between vertices (at most of size 2).  
G = { { a, b, c }, { {a, b}, {b, c}, {c, a} } } is a graph with vertices a, b and c and connection from a to b, b to c and c to a.  
- **Loops**: Edge E = { a, a } is called a loop
- **Adjacent**: Vertices connected are considered adjacent
- **Incident**: An edge is said to be incident on u if u is one of its endpoints
- **Degree**: The degree of a vertex v in a graph G, is equal to the number of edges which are incident with v

## Paths
A path P in a graph G(V,E) consists of an alternating sequence of vertices and edges of the form: 
    P = (v0, e1, v1, e2, v2, … , en, vn)
- **Length:**: The number of edges in a path is called the length of the path
- **Simple path:** A path P is called a simple path if all vertices in P are distinct
- **Trail:** A path P is called a trail if all edges are distinct
- **Closed path:** path P = (v0, v1, v2, ….. , vn) is called a closed path if v0 is equal to vn
- **Cycle:** A path P is called a cycle if it’s a closed path of length 3 or larger in which all vertices are distinct except v0 = vn
- **Distance**: the length of the shortest path between vertices u and v, written d(u,v)
- **Diameter**: the maximum distance between any two vertices in G, written diam(G)

## Connections
A graph G(V,E) is called connected if there is a path between any two vertices.
- **Bridge:** An edge e in a connected graph G is called a BRIDGE when removing e graph G - becomes disconnected
- **Cut point:** A vertex v in a connected graph G is called a CUTPOINT when removing v and all edges incident on v results in a disconnected graph
- **Traversable trail:** A path that contains a trail such that the trail starts and ends in 2 different vertices and uses all edges exactly once 

## Traversing
For traversable trails;
- **Even degree rule:** Let v be a vertex somewhere in the middle of the trail. Then you depart from v as often as you arrive in it. And every edge may be used only once. So deg(v) must be even.
- **Odd degree rule:** If s is the vertex where the trail starts or ends then you depart from s once more than you arrive in it. So deg(s) must be odd.
- **Traversability theorem:** A finite connected graph with two odd vertices is traversable. A traversable trail may begin at either odd vertex and will end at the other odd vertex.
- **Eulerain trial:** A traversable trail that starts and ends in the same vertex is called an EULERIAN TRAIL
- **Eulerain graph:** Any finite connected graph is Eulerian if and only if each vertex has an even degree

Fleury's algorithm can be used to find a traversable or eulerian trail.
- Pick vertex u as the starting point
- Pick an unused edge to traverse, pick {u,1}
- Check if {u,1} is a bridge?
  - No, then: add the edge to the temporary trail and remove it from the original graph    

## Directec graphs
All edges are assigned a direction. 
- Edge (u,v) is one-way. So it is only allowed to travel from u to v, but not the other way around. 
- Such edges we will write as an ordered pair!
- In this case u is called the origin or initial point and v is called the destination or terminal point
- v is also said to be a successor of u

**Weighted graphs** are graphs in which a number (the weight) is assigned to each edge

## Adcecency matrices
In computers, a graph can be represented by an adjacency matrix. 

![alt text](imgs/adcecency_matrices.png)

## BFS/DFS traversal

BFS = queue / list

![bfs_example](imgs/bfs_example.png)

DFS = stack / list

![dfs_example](imgs/dfs_example.png)

## Trees
A tree is a graph that is connected and if it has no cycles

If T is a tree with n vertices (n>1), then 
- T is connected
- T has no cycles
- T has n-1 edges 
- between any vertices v and w of T there is exactly one path
- adding an edge between two vertices in T creates a cycle
- every edge of T is a bridge

## Spanning Trees
A subgraph T of a connected graph G is called a spanning tree of G if T is a tree and T includes all vertices of G
- The spannign tree of G must contain all vertices found in G, and can ONLY include edges that are in the edges of G (so the edges of spanning tree must be a subset of edges of G) 
- **Minumum spannign tree**: a weighted spanning tree with the least weighted sum of the edges.

## Prims algorithm
- Choose a vertex v. This is your temporary tree T
- Repeat until all vertices are connected:
  1. Select an edge with minimum weight that has one vertex in T and the other vertex not in T
  2. Add this edge and its destination vertex to T, which gives you a new temporary tree T

## Kruskal of Algorithm
- Arrange the edges of G in order of increasing weight
- Start with only the vertices of G 
- Process the list of edges sequentially, add all edges that don’t result in a cycle

## Dijkstras Algorithm
Dijkstra’s algorithm builds a special spanning tree T. Only expand the temporary tree T using the ‘best’ vertices.
- Initially set l = infinity and p = {} for every vertex, except the starting vertex u which gets l = 0 and p = u
- Now repeat until the end-vertex w is part of the temporary tree T
  1. for all vertices in T consider all possible expansions 
  2. Expand T with that edge that has the smallest l of all possible expansions

## Rooted Tree's
A ROOTED TREE is a tree with a designated vertex that is called the ROOT
- Let G = ({r, s, t, u}, { {r, s}, {r, t}, {t, u} })
- G satisfies the definition of a tree (all be it a very small one)
- Let us make r the root. Now we have a rooted tree!

A rooted tree is directed, always! The direction is from the root to the vertices.
- From the root there is only one simple path to every other vertex.
- The root has indegree 0, all other vertices have indegree 1!!!
- All vertices with outdegree 0 we call leaves.
- Every vertex that is no leaf is called an internal vertex.

We draw a rooted tree with the root on the top and the edges downwards. And leave any arrows out.
In a rooted tree with root f, a branch Tf,(f,c) is the rooted tree that consists of f together with all vertices reachable from f using a path that starts with edge (f,c).

The length of a path P from the root to vertex v is called the level or depth of v 
The maximum vertex level is called the depth of the tree 

## Center and Centroid
The CENTROID is the set of vertices of which the maximum weight of all branches is as small as possible
- The WEIGHT of a branch Tv,e is equal to the number of edges in that branch. 
- The LEVEL  of a branch Tv,e is equal to the maximum distance from v to any of the leaves in the rooted tree
- It is also possible that it consists of 2 vertices. 

The CENTER is the set of vertices of which the maximum level of all branches is as small as possible.
- Finding the CENTER can also be done by removing leaves from the tree until the number of vertices left is <= 2

## Binary tree's
Specialized case of rooted tree's
- Vertex out degree <= 2
- Root is level 0 and the depth can be refered to as levels
- Usefull in compression 
- Sorting of binary tree's will not be on the exam (pre-oder, post-order, in-order)

## Hufmans Algorithm
Calculate unique, smaller encodings for unique information based on frequency of characters
In the algorithm
- all leaves contain a character
- see slide for calculating of this tree