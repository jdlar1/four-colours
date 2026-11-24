# Four colours around a pentagon

Can a short argument about one face replace some of the case analysis in a proof of the four-colour theorem? A pentagon is a natural place to try. Its boundary admits just ten colour patterns up to renaming. We can prove an exact counting relation among them, and exhibit a small obstruction to repairing a colouring in one move. Existence of a repair on an arbitrary exterior remains open in this argument.

## From a map to five terminals

Triangulate a planar map and take the planar dual. Its vertices have degree three. Tait's reformulation asks for an edge colouring of this cubic graph in which the three colours at every vertex differ. To see the correspondence, use the three nonzero elements of the group of binary pairs under XOR as edge colours. The difference of adjacent triangle-corner colours gives an edge label. Conversely, three distinct labels sum to zero around each triangle, so adding the labels along a path gives a vertex colour independent of the path on the sphere.

Take a simple pentagonal face with five edges leading out of it. Excise its five vertices, leaving those outgoing edges as terminals of the exterior, numbered 0 through 4 around the hole. All indices below are cyclic. We consider proper exterior colourings, including the terminal edges. Swapping two colours throughout one connected component of their edges preserves properness. Such a component is an alternating path or cycle.

**The pentagon extends exactly when the two singleton colours occupy neighbouring terminals.** To prove this, count incidences of a fixed colour at the internal vertices of the exterior. Every vertex contributes one. Each internal edge accounts for two incidences and each terminal for one. Thus the three terminal counts have the same parity. They sum to five, so they are 3, 1, 1.

Write the colours as A, B, C, with A repeated. Up to rotation, reflection and renaming, there are two cases. For adjacent singletons the spoke word is B C A A A. The successive pentagon edges *after* these spokes can be coloured A B C B C. Each spoke forces the next edge once the preceding edge is known, and only this initial choice works. For separated singletons the word is B A C A A. The edge between spokes B and A is forced to be C. At the next spoke A this forces the following edge to be B, and at spoke C the edge after that must be A. It collides with the next spoke A.

## A counting identity from one path swap

Let $a_i$ count labelled exterior colourings whose singleton positions are $i,i+1$. Let $b_i$ count those with singletons at $i,i+2$. Each count includes all six permutations of the colour names. Then

$$
a_i-b_i-b_{i-1} \quad\text{is independent of } i.
$$

**Proof.** Fix a position $k$ occupied by a singleton. Work first with names chosen so that C occurs at $k$, B is the other singleton, and A is repeated. The A–B edges meeting the boundary form two disjoint paths. Exactly one has the unique B terminal as an endpoint. Its other end is A. Swap A and B on that path. This moves the B singleton to the other end, keeps C fixed and gives an involution.

In order after $k$, the four available terminals are $k+1,k+2,k+3,k+4$. Planarity forbids the two paths from pairing the first with the third and the second with the fourth. In either remaining pairing, each path joins an odd slot to an even slot. The involution therefore pairs every colouring having B in an odd slot with one having B in an even slot. Restoring the six colour permutations gives

$$
a_k+b_{k-2}=b_k+a_{k-1}.
$$

Rearranging proves the identity. The argument allows internal two-colour cycles and places no bound on the size of the exterior.

**What it forces.** If the exterior has at least one colouring but none extends, every $a_i$ is zero. Then $b_k=b_{k-2}$ for every $k$. Since stepping by two visits all five positions, *all five bad patterns occur equally often*. The counting equations themselves allow positive equal counts on the five diagonals. A proof along this route needs some information they discard, such as which paths meet the same interior vertices.

## A nine-vertex obstruction to a one-swap repair

Draw an octagon with rim vertices 0 through 7 in cyclic order. Join a central vertex to 3, 5 and 7. Put outward terminals at 0, 1, 2, 4 and 6, numbered in that order. These instructions specify a planar exterior. Use this proper edge colouring.

| Edges in order | Colours |
| --- | --- |
| Rim, starting with 0–1 and ending with 7–0 | C B A C B C B A |
| Centre to 3, 5, 7 | B A C |
| Terminals 0 through 4 | B A C A A |

The B and C singleton terminals are separated. Here are all the possibilities for a first swap. The endpoint numbers refer to terminals, not rim vertices.

| Colour pair | Terminal pairs joined by its paths | Other components |
| --- | --- | --- |
| A, B | 1–3 and 0–4 | None |
| A, C | 1–4 and 2–3 | None |
| B, C | 0–2 | One internal cycle |

For A–B, the path 0–4 moves the B singleton to 4, still separated from C at 2. Swapping the other A–B path has the same singleton positions as swapping 0–4 followed by globally renaming A and B. The same reasoning for A–C moves the singleton at 2 to 3, still separated from B at 0. Either B–C move preserves the singleton positions. This exhausts every single-component swap.

**Two swaps suffice here.** Swap A–B on the path from terminal 1 to 3. The boundary becomes B B C B A. In that new colouring, swap B–C on the path from 0 to 1 (it uses rim edge 0–1). The boundary is now C C C B A, which extends. The intermediate move changes which terminals connect even though the pentagon still fails its extension test. That is a concrete reason to track interior paths as well as boundary words.

## Reproduce the example

Run `python3 four-colours/check.py` from the repository root. It enumerates the proper rim colourings of this single octagon. The third edge at every rim vertex is then forced. A breadth-first search starting from all extendible colourings gives the minimum number of component swaps for every exterior colouring.

| Minimum swaps | Labelled exterior colourings |
| --- | ---: |
| 0 | 36 |
| 1 | 36 |
| 2 | 12 |

The checker also tests the extension rule against all five-letter words. It uses the Python standard library and an eight-edge rim search with at most $3^8$ candidate assignments.

## Other directions and a next question

Fable also suggested assigning signs modulo three to cubic vertices and looking for compatible colourings of two triangulations of the same polygon. The sign approach seeks a vector satisfying the face equations with every coordinate nonzero. The polygon approach asks whether two independently triangulated sides admit the same boundary vertex colours. Both give alternatives if the pentagon counts lose too much information.

The [cap analysis](caps.md) answers the question left by the octagon example. A girth-five, cyclically 5-edge-connected graph can require three swaps. Enlarging the patch to include the neighbouring faces yields a finite reducibility argument for seven pentagon and hexagon arrangements.
