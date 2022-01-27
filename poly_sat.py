# Polymorphisms, SAT based appraoch

from functools import partial
from tkinter import W
from typing import Callable, Iterable, List, Set, Tuple
from pysat.solvers import Lingeling, Glucose3, Glucose4, Mergesat3, Minisat22, Cadical 
from itertools import product, combinations, permutations, chain
import time
import networkx as nx
import matplotlib.pyplot as plt
import copy
import numpy as np
from scipy import sparse
import sys


Solver = Glucose4 
# Solver = Lingeling
# Solver = Cadical

class RelationalStructure:
    def __init__(self, domain: list, relations: list):
        self.domain = domain
        self.relations = relations

    def __mul__(self, other: 'RelationalStructure'):
        return RelationalStructure(
            domain=list(map(",".join, product(self.domain, other.domain))),
            relations=[[[rela[0] + relb[0], rela[1] + relb[1]] for relb in relbs for rela in relas] 
                        for (relas, relbs) in zip(self.relations, other.relations)]
        )

G = RelationalStructure(
    domain=["a","b","c"],
    relations=[[["a","b"],["b","c"],["c","a"]]]
)
H = RelationalStructure(
    domain=["q","r","s"],
    relations=[[["q","r"],["r","s"]]]
)


class Digraph:
    def __init__(self, vertices: list, edges: list, directed=True) -> None:
        self.vertices: set = vertices
        self.edges: set = edges
        self.directed: bool = directed

    def __repr__(self) -> str:
        return f"Digraph with {len(self.vertices)} vertices."
        # return self.__str__()

    def __str__(self) -> str:
         return f"G = Digraph(\n" \
                f"    vertices={self.vertices},\n" \
                f"    edges={self.edges}\n" \
                f")"     

    def __mul__(self, other: 'Digraph') -> 'Digraph':
        if self.directed and other.directed:
            return Digraph(
                # vertices=set(map("".join, product(self.vertices, other.vertices))),
                vertices=set(map(",".join, product(self.vertices, other.vertices))),
                edges=set((self_edge[0] + "," + other_edge[0], self_edge[1] + "," + other_edge[1]) for other_edge in other.edges for self_edge in self.edges)
            )

        elif self.directed != other.directed:
            raise Exception("Cannot multiply directed with undirected graphs!")

        def check(u, v):
            return (
                (v[:n],u[:n]) in self.edges and (v[n:],u[n:]) in other.edges or
                (v[:n],u[:n]) in self.edges and (u[n:],v[n:]) in other.edges or
                (u[:n],v[:n]) in self.edges and (v[n:],u[n:]) in other.edges or
                (u[:n],v[:n]) in self.edges and (u[n:],v[n:]) in other.edges
            )

        n = len(list(self.vertices)[0])
        new_vertices = set(map(",".join, product(self.vertices, other.vertices)))
        new_edges = [(min(v,u),max(v,u)) for v in new_vertices for u in new_vertices if check(u,v)] 
 
        return Digraph(
            vertices=set(new_vertices),
            edges=set(new_edges),
            directed=False
        )


    def __pow__(self, p: int) -> 'Digraph':
        if p < 1: raise "Not valid!"
        H = Digraph(vertices=self.vertices, edges=self.edges, directed=self.directed) 
        for _ in range(p-1): H*=self
        return H   
    
    def __eq__(self, other: 'Digraph') -> bool:
        return True if self.vertices == other.vertices and self.edges == other.edges else False

    def to_matrix(self) -> np.ndarray:

        # important for the vertices to be sorted in this instance, for when handling direct product of lists of vertices
        vertices = sorted(list(self.vertices))
        vertex_numbering = {idx: vertex for idx, vertex in enumerate(vertices)}
        n = len(self.vertices)
        matrix = np.zeros((n,n), dtype=np.int8)
        for i in range(n):
            for j in range(n):
                if (vertex_numbering[i], vertex_numbering[j]) in self.edges:
                    matrix[i, j] = 1
                    matrix[j, i] = 1   # symmetry, s.t. works for undirected graphs too
        return matrix


def from_matrix(mat: np.ndarray) -> Digraph:
    n = mat.shape[0]
    vertices = [str(i) for i in range(1, n+1)]
    edges = []
    for i in range(n):
        for j in range(n):
            if mat[i][j] == 1:
                edges.append[(vertices[i], vertices[j])]
    return Digraph(
        vertices=set(vertices),
        edges=set(edges)
    )



class Polymorphism():
    def __init__(self, G: Digraph, H: Digraph) -> None:
        self.G: Digraph = cvt2str(G)
        self.H: Digraph = cvt2str(H)
        self.morphism: list = None
        # self.formula: Solver = solver

    @staticmethod
    def print_mapping(homomorphism: dict = None, function_symbol: str ="f") -> None:
        print(", ".join(sorted([f"{function_symbol}({m})={homomorphism[m]}" for m in homomorphism])))

    def uniqueness_of_mapping(self, u: str, H_vertex_list: list, formula, map_vars: list) -> None:
        # more efficient method of obtaining alpha 2
        for i, v1 in enumerate(H_vertex_list[:-1]):
            for v2 in H_vertex_list[(i+1):]:
                formula.add_clause([-map_vars[(u, v1)], -map_vars[(u, v2)]])

    
    def standard_uniqueness_vars(self, G: Digraph, H: Digraph, edge_comb: list, map_vars: dict, formula: Solver) -> None:
        """
        Variables ensuring each vertex of G is mapped to one and only one vertex in H
        """
        H_vertex_list = list(H.vertices)

        for u in G.vertices:
            formula.add_clause([map_vars[(u, v)] for v in H.vertices])

            # Possibilities: (u,1), (u,2), (u,3), or (u,4)  -- ONLY ONE!
            #                  F      F       F       T  
            # (u,1) -> not(u,2), (u,1) -> not(u,3), (u,1) -> not(u,4)
            # (u,2) -> not(u,3), (u,2) -> not(u,4)
            # (u,3) -> not(u,4) 

            # Note: (u->v) = (not u or v), so (u->not v) = (not u or not v)
            # self.uniqueness_of_mapping(u, H_vertex_list, map_vars, formula)
            for i, v1 in enumerate(H_vertex_list[:-1]):
                for v2 in H_vertex_list[(i+1):]:
                    formula.add_clause([-map_vars[(u, v1)], -map_vars[(u, v2)]])


    def general_mapping_clauses(self, G_vertices: List[str], H_vertices: List[str], map_vars: dict, formula: Solver, poly_vertices: Callable, share) -> None:
        l = len(H_vertices)
        seen = set()

        # f(u1) = v  =>  f(u2) = v   -- i.e., clause for special polymorphisms indicating if u1 is mapped to v, then u2 must also be mapped to v
        map_implies   = lambda v, u1, u2: formula.add_clause([-map_vars[(u1, v)], map_vars[(u2, v)]])
        map_iff       = lambda v, u1, u2: (map_implies(v, u1, u2), map_implies(v, u2, u1))  # same as above but now if and only if

        # clause to ensure u (in G) is mapped to at least one vertex v of H (represents existence of mapping)
        exist_clause  = lambda u: formula.add_clause(list(map(lambda v: map_vars[(u, v)], H_vertices))) 

        # clause saying: if f(u) = vi, then f(u) != vj, where vi and vj are the i-th and j-th vertices of H, respectively
        unique_clause  = lambda u, i, j: formula.add_clause(
            [-map_vars[(u, H_vertices[i])], -map_vars[(u, H_vertices[j])]]
        )
        unique_clauses = lambda u, i: list(map(lambda j: unique_clause(u, i, j), range(i + 1, l)))

        for u in G_vertices:
            if share[u] not in seen:
                seen.add(u)
                
                # if (u_poly := poly_vertices(u)):
                #     if isinstance(u_poly, str):
                #         u_poly = [u_poly]
                #     for u_p in u_poly:
                #         if u_p not in seen: #and u_p in G_vertices:
                #             seen.add(u_p)
                #             for v in H_vertices:
                #                 map_iff(v, u, u_p)
                
                for i in range(l):
                    unique_clauses(u, i)
                exist_clause(u)

    def edge_preservation_clauses(self, G: Digraph, H: Digraph, G_vertices: List[str], edge_prod: List[Tuple[str, str]], map_vars: dict, formula: Solver, arity: int, share: dict, directed: bool = False) -> None:
        # obtain clauses pertaining to structure preservation 

        # obtain the pairs of vertices of H that are not edges of H
        def isin(edge, graph):
            if graph.directed: return True if edge in graph.edges else False
            return True if (min(edge), max(edge)) in graph.edges else False
        not_H_edges = [eh for eh in edge_prod if not isin(eh, H)]

        # obtain sparse matrix representation of G^arity
        Gmat = sparse.csr_matrix(G.to_matrix())
        Gmat_ = copy.deepcopy(Gmat)
        for _ in range(arity - 1):
            Gmat_ = sparse.kron(Gmat_, Gmat)
        if not directed:
            # If we're dealing with undirected graphs, we need only the upper right half of the adjacency matrix for edges
            Gmat_ = sparse.triu(Gmat_)
        Gmat_edges = Gmat_.nonzero()
        l = len(Gmat_edges[0])
        print(f"Obtained sparse matrix for edges of G^{arity}.")

        # construct the clauses
        seen = set()
        skipped = 0
        for i in range(l):
            Gedge = (G_vertices[Gmat_edges[0][i]], G_vertices[Gmat_edges[1][i]])
            if not directed:
                shared_edge = (min(share[Gedge[0]], share[Gedge[1]]), max(share[Gedge[0]], share[Gedge[1]]))
            else:
                shared_edge = (share[Gedge[0]], share[Gedge[1]])
            if shared_edge[0] == shared_edge[1]:
                # If this is so, then there cannot be a polymorphism of the kind we want! Thus, add a contradiction and stop
                formula.add_clause([1])
                formula.add_clause([-1])
                break
            if shared_edge not in seen:
                seen.add(shared_edge)
                for eh in not_H_edges:            
                    formula.add_clause([-map_vars[(Gedge[0],eh[0])], -map_vars[(Gedge[1],eh[1])]])
                    if not directed:
                        formula.add_clause([-map_vars[(Gedge[1],eh[0])], -map_vars[(Gedge[0],eh[1])]])
            else:
                skipped += 1
        print(f"Number of edges skipped: {skipped}")

    def reduction_to_sat(self, G=None, H=None, arity=1, special=None, verbose=False, silent=False, directed=False) -> None:


        if G is None:
            G = self.G
        if H is None:
            H = self.H

        print(f"Searching for an arity {arity} {special} polymorphism from a graph")

        t = time.time()
        if not silent: print("Commencing reduction.")
        formula = Solver()

        # obtain the vertices of G^{arity} -- sorting is important (to match kronecker product of matrix later)
        Gvs = sorted(list(G.vertices))
        G_vertices = copy.deepcopy(Gvs) 
        for _ in range(arity - 1):
            G_vertices = list(map(",".join, product(G_vertices, Gvs)))


        # print(len(G.vertices))
        # if special == "siggers":
        #     G.vertices = set([v for v in G.vertices if is_siggers_style(v)])
        #     G.edges = set([e for e in G.edges if (e[0] in G.vertices and e[1] in G.vertices)])
        # print(len(G.vertices))

        H_vertices = list(H.vertices)
        n, m = len(G_vertices), len(H_vertices)        
        edge_prod = list(product(H_vertices, H_vertices))
        edge_comb = list(combinations(sorted(list(H_vertices)), 2))
        possible_maps = list(product(G_vertices, H_vertices))   
         
        map_vars = {
            mapping: variable + 1 for variable, mapping in enumerate(possible_maps) 
        }

        # print(len(possible_maps))

        # Variables to ensure edges in G are mapped to edges in H
        # Variables ensuring each vertex of G is mapped to one and only one vertex in H
        # Can use a match-case statement here...

        if special is None: 
            self.standard_uniqueness_vars(G, H, edge_comb, map_vars, formula)
            share = {u: u for u in G_vertices}
        else:
            if   special == "cyclic":      poly_func = cycles_of_string
            elif special == "siggers":     poly_func = siggers_perm
            elif special == "wnu":         poly_func = wnu_strings
            elif special == "ts":          poly_func = symmetric_strings
            elif special == "olsak":       poly_func = olsak_strings
            elif special == "sub_siggers": poly_func = sub_siggers
            else: raise Exception(f"Unknown special polymorphism type: {special}.")

            # have polymorphism variables share mappings
            print(f"Number of unique propositional variables: {len(set(map_vars.values()))}")
            share = dict()
            seen = set()
            for u in G_vertices:
                if u not in seen:
                    share[u] = u
                    # seen.add(u)
                    if (u_poly := poly_func(u)):
                        if isinstance(u_poly, str):
                            u_poly = [u_poly]
                        for u_p in u_poly:
                            if u_p not in seen: #and u_p in G_vertices:
                                seen.add(u_p)
                                share[u_p] = u
                                for v in H_vertices:
                                    map_vars[(u_p, v)] = map_vars[(u, v)]

            print(f"Number of unique propositional variables: {len(set(map_vars.values()))}")
            self.general_mapping_clauses(G_vertices, H_vertices, map_vars, formula, poly_func, share)
        
        if not silent: print("Obtained general mapping clauses.")
        self.edge_preservation_clauses(G, H, G_vertices, edge_prod, map_vars, formula, arity, share, directed)

        # Obtain clauses pertaining to preservation of edges
        if not silent: print("Obtained edge preservation clauses.")

        if not silent: print("The problem has been reduced to SAT; commmencing SAT solving.")
        if not silent: print(f"(Reduction took {time.time() - t:.3f} seconds.)")

        t = time.time()
        s = formula.solve()
        if not silent: print("The formula has been solved.")
        if not silent: print(f"(SAT solving took {time.time()-t:.3f} seconds.)")
        nt = "NOT "
        hm = "homomorphism"
        pl = "polymorphism"
        of = f" of arity {arity}"
        spec = "" if special is None else special+" "
        if not silent: print(f"There does {(not s)*nt}exist a {spec}{pl if arity > 1 else hm}{(arity is not None)*of}.")
        if s:
            model = formula.get_model()
            the_homomorphism = dict()
            for val in model[:n*m]:
                if val > 0:
                    the_homomorphism[possible_maps[val-1][0]] = possible_maps[val-1][1] 
            self.morphism = the_homomorphism
        if verbose:
            self.print_mapping(the_homomorphism)     
        return s


    def print_map(self) -> None:
        if self.morphism is not None:
            self.print_mapping(self.morphism)
        else:
            raise Exception("No homomorphism or polymorphism found (yet).")

    def print_cycles(self, base: str) -> list:
        """
        Sanity check when searching for cyclic polymorphisms
        """
        if self.morphism is not None:
            if base not in self.morphism:
                raise Exception("Invalid base.")
            return [f"f({cyc})={self.morphism[cyc]}" for cyc in cycles_of_string(base)]
        else:
            raise Exception("No homomorphism or polymorphism found (yet).")

    def print_siggers(self, base: str) -> list:
        """
        Sanity check for siggers polymorphisms.
        """
        if self.morphism is not None:
            if base not in self.morphism:
                raise Exception("Invalid base.")
            base_siggers = siggers_perm(base)
            return [f"f({base})={self.morphism[base]}", f"f({base_siggers})={self.morphism[base_siggers]}"]
        else:
            raise Exception("No homomorphism or polymorphism found (yet).")

    def print_olsak(self, base: str):
        """
        Sanity check for Olšák polymorphisms 
        """
        if self.morphism is not None:
            if base not in self.morphism or not (olsak := olsak_strings(base)):
                raise Exception("Invalid base.")
            return [f"f({s})={self.morphism[s]}" for s in [base] + olsak]
        else:
            raise Exception("No homomorphism or polymorphism found (yet)")


    def print_symmetries(self, base: str) -> list:
        if self.morphism is not None:
            if base not in self.morphism:
                raise Exception("Invalid base.")
            return [f"f({sym})={self.morphism[sym]}" for sym in symmetric_strings(base)]


    def find_polymorphism(self, arity=2, directed=True, special=None, verbose=False, get_power=True, silent=False):
        # endo = self.G == self.H
        G = copy.deepcopy(self.G) 
        H = copy.deepcopy(self.H)
        self.original_vertices_G = list(cvt2str(G).vertices)
        if get_power:
            t = time.time()
            G = G**arity
            if not silent: 
                print(f"Time taken to obtain graph power: {time.time() - t:.3f} seconds.")
        if not directed:
            t = time.time()
            G = cvt2undirected(G)
            H = cvt2undirected(H)
            print(f"Time taken to convert graphs to undirected form: {time.time() - t:.3f}")
        s = self.reduction_to_sat(G=G, H=H, arity=arity, special=special, verbose=verbose, silent=silent, directed=directed)
        return s

    def has_homomorphism(self):
        self.reduction_to_sat(self.G, self.H, arity=1)



"""
Various helper functions
"""

def is_edge(s: str, t: str, R: Set[Tuple[str, str]], arity: int) -> bool:
    """
    Check if an edge exists between two higher dimensional vertices
    """
    ls = s.split(",")
    lt = t.split(",")
    for i in range(arity):
        if (ls[i], lt[i]) not in R:
            return False 
    return True


def cycles_of_string(s: str) -> list: 
    l = s.split(",")
    return [",".join(l[i:]+l[:i%len(l)]) for i in range(len(l))]

def is_siggers_style(s: str) -> bool:
    l = s.split(",")
    if len(l) == 6: 
        if (l[0] != l[2] or l[1] != l[4] or l[3] != l[5]) and (l[0] != l[5] or l[1] != l[3] or l[2] != l[4]):
           return False
    elif len(l) == 4:
        if (l[1] != l[2]) and (l[1] != l[3]):
            return False
    else:
        raise "Must be arity 4 or 6 for Siggers....!!!!"  
    return True     


def siggers_perm(s: str) -> str:
    l = s.split(",")
    if len(l) == 6: 
        if l[0] != l[2] or l[1] != l[4] or l[3] != l[5]:
           return False
           # raise Exception("No Siggers permutation for such a string.")
        x, y, z = l[0], l[1], l[3]
        return f"{y},{x},{z},{x},{z},{y}" 
    elif len(l) == 4:
        if l[1] != l[2]:
            return False 
        x, y, z = l[0],l[1],l[3]
        return f"{y},{x},{z},{x}"
    else:
        raise Exception("Siggers polymorphisms must be 6-ary or 4-ary.")


def sub_siggers_vertices(vertex_list: List[str]) -> List[str]:
    g = lambda l: l[0] == l[2]
    f = lambda v: g(v.split(','))
    return [v for v in vertex_list if f(v)]


def sub_siggers(s: str, z: str) -> str:
    l = s.split(',')
    x = l[0]
    y = l[1]
    return f"{y},{x},{z}"
    # return (f'{z},{y},{z}', f'{y},{x},{z}', f'{x},{z},{y}')



def wnu_strings(s: str) -> list:
    l = s.split(",")
    if len(l) == 1:
        return False
    y = l[0]
    if any(y == x for x in l[1:]):
        return False
    x = l[1]
    if any(x != x_ for x_ in l[1:]):
        return False
    return cycles_of_string(s)

def symmetric_strings(s: str) -> list:
    l = s.split(",")
    return [",".join(sym) for sym in permutations(l)]

def olsak_strings(s: str) -> list:
    l = s.split(",")
    if len(l) != 6:
        raise Exception("Olšák polymorphisms must be 6-ary.")
    x, y = l[0], l[2]
    if x != l[1] or x != l[5] or y != l[3] or y != l[4]:
        return False 
    return [f"{x},{y},{x},{y},{x},{y}", f"{y},{x},{x},{x},{y},{y}"]


def custom_polymorphism(strings: list) -> list:
    base = strings[0]
    base_l = base.split(",")
    base_i = list(map(base_l.index, base_l))
    indices_dict = {base_l[i]: base_i for i in range(len(base_l))}

    unique_chars = list(set(base_l))
    indices = {c: [i for i, l in enumerate(base) if l == c] for c in unique_chars}



def cvt2str(G: Digraph) -> Digraph:
    return Digraph(
        vertices=set(map(str, list(G.vertices))),
        edges=set(map(lambda e: (str(e[0]), str(e[1])), list(G.edges)))
    )


def cvt2undirected(G: Digraph) -> Digraph:
    return Digraph(
        vertices=G.vertices,
        edges=set((min(e), max(e)) for e in G.edges),
        directed=False
    )


def K(n: int, m: int = None, directed: bool = True) -> Digraph:
    """
    Return a complete graph with k vertices
    """
    if m is None:
        vertices = [str(i) for i in range(1,n+1)] 
        return Digraph(
            vertices=set(vertices),
            edges=set([(i,j) for i, j in product(vertices, vertices) if i != j])
        )
        

def C(n: int, directed: bool = True) -> Digraph:
    """
    Return an undirected cycle with k vertices
    """
    if n == 1:
        return Digraph(vertices={'1'}, edges=set()) 
    vertices = [str(i) for i in range(1,n+1)]
    return Digraph(
        vertices=set(vertices),
        edges=set(
            chain.from_iterable(
                [[(str(i), str(i % n + 1)), (str(i % n + 1), str(i))] for i in range(1, n + 1)]
            )
        )
    )

clique = lambda k: K(k)
cycle = lambda k: C(k)



def print_special_polymorphisms() -> None:
    print("cyclic, weak near unanimity (wnu), totally symmetric (ts), siggers, olsak")


"""
Various graphs
"""

loop = Digraph(
    vertices={1},
    edges={(1,1)}
)

C_1  = C(1)
C_2  = C(2)
C_3  = C(3)
C_4  = C(4)
C_5  = C(5)
C_6  = C(6)
C_7  = C(7)
C_8  = C(8)
C_9  = C(9)
C_10 = C(10)
vertex   = C_1
edge     = C_2
triangle = C_3
square   = C_4
pentagon = C_5 
hexagon  = C_6 
heptagon = C_7 
octagon  = C_8 
nonagon  = C_9
decagon  = C_10

K_3 = K(3)
K_4 = K(4)
K_5 = K(5)
K_6 = K(6)
K_7 = K(7)
K_8 = K(8)
K_9 = K(9)



nu4 = Digraph(
    vertices={'1','2','3','4'},
    edges={
        ('1','2'),('1','3'),('1','4'),
        ('2','3'),('2','4'),
        ('4','1'),('4','2'),('4','4')
    }
)



nu3 = Digraph(
    vertices={'0','1'},
    edges={
        ('0','1'),
        ('1','0'),('1','1')
    }
)


sea_devil = Digraph(
    vertices={1,2,3,4,5,6},
    edges={
        (1,2),(2,4),
        (3,1),(3,2),
        (4,3),(4,5),
        (6,5),(6,6)
    }
)

test = [
    [1,0,0,0],
    [0,0,0,1],
    [1,0,0,0],
    [0,1,0,1]
]


test1 = [
    [0,1,0],
    [1,0,1],
    [0,1,0]
]

test = cvt2str(Digraph(
    vertices={1,2,3,4},
    edges={(1,1),(2,4),(3,1),(4,2),(4,4)}
))

test1 = cvt2str(Digraph(
    vertices={1,2,3},
    edges={(1,2),(2,1),(2,3),(3,2)}
))


def directed_get_connected_components(G):
    if isinstance(G, Digraph):
        Gnx = nx.DiGraph() 
        Gnx.add_edges_from(G.edges)
    elif not isinstance(G, nx.DiGraph):
        Gnx = nx.DiGraph(G)
    components = []
    for c in nx.weakly_connected_components(Gnx):
        subgraph = nx.subgraph(Gnx, c)
        components.append(Digraph(
            vertices=c,
            edges=set(nx.edges(subgraph))
        ))
    return components 


def undirected_get_connected_components(G):
    if isinstance(G, Digraph):
        Gnx = nx.Graph() 
        Gnx.add_edges_from(G.edges)
    elif not isinstance(G, nx.Graph):
        Gnx = nx.Graph(G)
    components = []
    for c in nx.connected_components(Gnx):
        subgraph = nx.subgraph(Gnx, c)
        components.append(Digraph(
            vertices=c,
            edges=set(nx.edges(subgraph))
        ))
    return components 


def solve_via_subgraphs(H, G, arity, directed: bool = True):
    l = []
    for c in undirected_get_connected_components(cvt2undirected(cvt2str(G)**arity)):
        l.append(Polymorphism(H=H, G=c).find_polymorphism(arity=arity, directed=directed, special='siggers', get_power=False, silent=False))
    return l




if __name__ == '__main__':
    H = eval(sys.argv[1])
    G = eval(sys.argv[2])
    arity = eval(sys.argv[3])
    special = sys.argv[4]
    if len(sys.argv) > 5:
        directed = eval(sys.argv[5])
    else:
        directed = False
    if len(sys.argv) > 6:
        silent = eval(sys.argv[6])
    else:
        silent = False

    r = Polymorphism(H=H, G=G).find_polymorphism(arity=arity, directed=directed, special=special, get_power=False, silent=silent)
    


# ar = 6
# r = Polymorphism(H=K(4), G=C_11).find_polymorphism(arity=ar, directed=False, special='ts', get_power=False, silent=False)



# r = Polymorphism(H=sea_devil, G=sea_devil).find_polymorphism(arity=ar, directed=True, special='siggers', get_power=False, silent=False)

# l = solve_via_subgraphs(H=clique(4), G=cycle(7), directed=False, arity=ar)
# print(all(l))

# r = Polymorphism(H=cvt2str(C_6)**3, G=cvt2str(C_6)**4).find_polymorphism(arity=1, special='wnu', get_power=True, silent=False)
# r = Polymorphism(H=cvt2str(K_4), G=cvt2str(C_6)).find_polymorphism(arity=ar, special='wnu', get_power=True, silent=False)
# print(r)



# G = nx.Graph() 
# G.add_edges_from((cvt2str(C_3)**3).edges)

# nx.draw(G)
# plt.show()


# G = nx.Graph()
# G = nx.DiGraph()
# G.add_edges_from((cvt2str(nu4)**4).edges)
# print(G)



# print(len((cvt2str(C_7)**7).vertices))




# l = np.array([
#     [0,1,0],
#     [0,0,1],
#     [1,0,0]
# ])

# print(np.kron(l, l))

# exit()
# exit()

# m = (cycle(3)).to_matrix()
# print(np.kron(m, m))

exit()

c7 = sparse.csr_matrix(cvt2undirected(cycle(7)).to_matrix())
c7_ = copy.deepcopy(c7)
for i in range(5):
    c7_ = sparse.kron(c7_, c7, format='csr')



print(c7_)
print(c7_.shape[0])
# n = 0
# for i in range(len(c7_.nonzero())):
#     n += 1
    # n /= (i+1) 
# print(n)

nz = c7_.nonzero()
print(len(nz[0]))
nz = sparse.triu(c7_).nonzero()
rows, cols = nz 
# c7_[rows, cols] = c7_[cols, rows]
# nz = c7_.nonzero()
# print(c7_)

print(len(nz[0]))


# for e in c7_:
#     print(e)
#     exit()


# print(c7_.shape[0])
# v = sorted(list(cycle(7).vertices))
# vc = copy.deepcopy(v)
# for _ in range(5):
#     vc = list(map(",".join, product(vc, v)))

# print(len(vc))

# print(vc[0], vc[19608])
# print(vc[0], vc[19608])
# print(vc[117648], vc[98040])

# print(vc[:10])