# What can we repair around a pentagon?

A pentagon in a cubic plane graph can resist two successive Kempe swaps even when the graph has girth five and is cyclically 5-edge-connected. A larger patch behaves better. A pentagon surrounded by five pentagons accepts every colourable exterior *with its colours fixed*. If some neighbours are hexagons, the exterior may need swaps. A finite boundary argument still works for every arrangement with at least one pentagonal neighbour and all the other neighbours pentagonal or hexagonal.

These statements concern the ordinary embedded patch described below, with distinct rim vertices and five distinct spokes. The extension claims quantify over **every** proper exterior colouring. No assumption about the sizes of the faces beyond the rim enters their proofs.

## A cap that accepts every exterior colouring

Draw a pentagon inside a decagon. Join the five pentagon vertices in cyclic order to the five odd-numbered decagon vertices. The even vertices have one edge apiece leading to the exterior. Call the pentagon, spokes and rim together the cap. We can replace every edge colour inside the cap while keeping all five exterior edges fixed.

**Lemma.** Every admissible labelled boundary colouring has exactly two completions across the cap.

**Proof of existence.** As in the [five-terminal argument](README.md), the boundary colours have multiplicities 3, 1, 1. Up to symmetry and colour names, only two words need checking. Number the rim from 0 to 9. In both examples below, read the rim colours starting with the edge from 0 to 1. At each vertex the third colour is forced by its two rim edges.

| Exterior colours, at even vertices | Rim colours | Forced inward spokes, at odd vertices |
| --- | --- | --- |
| B C A A A | A B A C B C B C B C | C B A A A |
| B A C A A | A B C A B C B C B C | C B A A A |

The same inward word works in both cases. Its singletons are adjacent, so it fills the central pentagon in exactly one way. The two rows already prove extension for all possible exteriors.

**Counting the completions by hand.** At each even vertex, the exterior colour specifies the two incident rim colours as an unordered pair. Choose their clockwise order. Consecutive even vertices carrying the same exterior colour must have the same order, because their shared odd neighbour requires two different colours. Thus BCAAA has only three blocks to orient and BACAA has four. Discard an orientation whenever it gives the same colour to the two edges at an odd vertex. The resulting inward words, with one rim assignment per entry, are

| Exterior word | Inward words with adjacent singletons | Inward words with separated singletons |
| --- | --- | --- |
| BCAAA | CBAAA, BAAAC | ACAAB, ABAAC |
| BACAA | CBAAA, BCAAA | CABAA, ABAAC, AACAB, AABAC |

Only the middle column fills the central pentagon. In particular a fixed exterior can always be completed by recolouring these fifteen vertices, regardless of how large the exterior is.

## Letting neighbouring faces have six sides

In a larger rim, write down the five distances from one inward spoke to the next, measured in rim edges. A gap of 2 makes the neighbouring face a pentagon. A gap of 3 makes it a hexagon. A pattern such as 32322 describes the five gaps in cyclic order, starting at an inward spoke at vertex 0. All remaining rim vertices carry exterior terminals. If there are $k$ terminals the rim has $k+5$ vertices.

The cap with one hexagonal neighbour already rejects a fixed boundary. Number its six exterior terminals clockwise starting just after inward spoke 0, with gap pattern 32222. AAAAAA has no completion. To understand how planarity helps, trace the A–B paths through any exterior with that word. They pair the six terminals without crossings. Every such matching has an adjacent pair (take a shortest enclosed interval). Swapping A and B on that path produces exactly two adjacent B terminals. All six placements of that pair fill the cap, as can be checked by the rim rule above. The exterior may be arbitrarily large. The six-point matching suffices to choose the repair.

The following argument applies that reasoning to *all* boundary words.

1. List the words in which each of A, B and C occurs with the parity of $k$. Incidence counting forces this parity in every properly coloured exterior. Forget colour names and retain the order of the terminals.
2. Mark each word that already fills the cap. Enumerate proper cyclic rim words, read the forced inward spokes and keep the assignments with adjacent singleton spokes. The remaining spokes give the exterior word.
3. For an unmarked word, choose two colours. Its terminals of these colours must be paired by disjoint exterior paths. Consider **every** noncrossing pairing. For each pairing, look for a subset of its paths whose simultaneous swaps yield a previously marked word. The choice of subset may depend on the pairing. Mark the original word if one choice of colours works for every pairing.
4. Repeat with the words from the preceding round available. Induction on the marking round proves the claimed repair. The actual exterior supplies one of the listed pairings. Swaps within a subset use disjoint components, so they can be made successively. Further rounds use the pairings of the resulting colouring.

The finite calculation below covers the eight cyclic arrangements up to reflection. A round can contain several swaps. The counts distinguish terminal positions and identify global permutations of A, B and C.

| Gaps | Boundary classes | Fill immediately | Further rounds before stopping | Left undecided |
| --- | ---: | ---: | ---: | ---: |
| 22222 | 10 | 10 | 0 | 0 |
| 32222 | 31 | 22 | 2 | 0 |
| 33222 | 91 | 47 | 3 | 0 |
| 32322 | 91 | 52 | 2 | 0 |
| 33322 | 274 | 104 | 4 | 0 |
| 33232 | 274 | 118 | 4 | 0 |
| 33332 | 820 | 257 | 6 | 0 |
| 33333 | 2,461 | 530 | 15 | 1,220 |

**Consequence for a hypothetical smallest counterexample.** Any of the first seven embedded caps could be removed and replaced by a simple $k$-cycle attached to the same terminals in order. This gives a smaller planar cubic graph. It is bridgeless if the original was bridgeless. The new cycle edges lie on a cycle, and any excursion of an old cycle through the removed patch can be rerouted through the replacement. More explicitly, the endpoints of any retained edge are still connected after deleting it, since the replacement connects all attachments. The smaller graph therefore supplies a proper colouring by minimality. Restrict it to the exterior, then apply the cap repair. This excludes all seven patches from a smallest counterexample.

**Limit of the argument.** For five hexagonal neighbours, the 1,220 surviving classes form a precise obstruction to this marking rule. At each surviving word, for each choice of two colours, there exists a noncrossing pairing for which *every* subset swap stays among the survivors. The pairing choices may be incompatible with one another in a single planar exterior. A proof using this patch would benefit from a constraint linking the three pairings. A general proof would also have to handle larger neighbouring faces or prove an unavoidable family of reducible configurations.

## A three-swap example with no triangles or squares

Draw four concentric cycles of lengths 5, 10, 10, 5 from top to bottom, with indices starting at zero on each cycle. Join upper pentagon vertex $i$ to first decagon vertex $2i$, first decagon vertex $2i+1$ to second decagon vertex $2i$, and second decagon vertex $2i+1$ to lower pentagon vertex $i$. These links preserve cyclic order. Delete the upper pentagon and treat its five links as terminals.

| Edges in order | Colours |
| --- | --- |
| First decagon | ABACABABCB |
| Second decagon | BCABABABCA |
| First to second decagon | CBCCA |
| Lower pentagon | BABAC |
| Second decagon to lower pentagon | ACCCB |
| Terminals | CCBCA |

There are seven choices of first component, including two A–B cycles entirely inside the exterior. From this colouring, neither the initial state nor any state one or two swaps away has adjacent singletons. The [witness checker](three_swaps.py) verifies that lower bound by exhausting just the first two moves. For the upper bound, number the edges of the first decagon starting at edge 0–1. Perform A–B on the component of edge 0, A–C on the component of edge 1, then A–B on the component of edge 2. The terminal words are CCBCA, CABAA, CBAAA after the respective moves. The first swap changes only an interior cycle, yet it helps unlock the boundary.

**Girth.** The four rings have length at least five. A cycle using links between rings crosses some interface twice. To have length at most four it would have to use exactly two links and one rim edge on either side, since no vertex belongs to two links. On the decagon side of that interface its two attachment vertices have the same parity and cannot be adjacent. The pentagons give girth exactly five.

**Cyclic edge connectivity.** Suppose at most four cut edges divide the graph into two vertex sets. Each ring split by this partition costs at least two cut edges. Thus at least two rings are unsplit. All unsplit rings lie on the same side: there are five edge-disjoint longitudinal paths, one per index $i$, meeting every ring via its $i$th pentagon vertex or its decagon edge $2i$–$2i+1$. Putting two whole rings on opposite sides costs at least five edges.

The other side can have a cycle only if it occupies two adjacent split rings, since a proper subset of one ring is a forest. Two split rings consume all four cut edges, so each occupied part is one interval and no inter-ring link crosses the cut. At least one of these two rings is a decagon with an unsplit neighbour on its other side. The occupied interval must avoid the five vertices linked to that unsplit neighbour. Those five alternate, so the interval has at most one vertex. It contributes at most one link to the other occupied ring, which itself induces a path. Hence there is no cycle on that side. This proves the claimed connectivity without enumerating cuts.

## Reproduce

Run `python3 four-colours/caps.py` for the cap table and `python3 four-colours/three_swaps.py` for the distance-three witness. Both use the Python standard library. The cap computation stores only boundary information and rim assignments independent of the size of the exterior. The construction and the finite reducibility check make no claim of historical novelty.
