
# Definitions and Proofs in latex
## Def. Topology
Let $X$ be some set and $\mathcal{T}\subseteq \mathcal{P}(X)$ be a collection
Then $\mathcal{T}$ is a topology iff
1. $X\in \mathcal{T}$ 
2. $\forall A\subseteq \mathcal{T}:|A|<\infty \Rightarrow \bigcap\limits_{a \in A}a \in \mathcal{T}$ 
3. $\forall A \subseteq \mathcal{T}: \bigcup\limits_{a\in A}a \in \mathcal{T}$ 

We call $X$ a topological space iff it has a topology
For a topology $\mathcal{T}$ we call $A\in \mathcal{T}$ open

## Def. Closed
$Y\subseteq X$ is said to be closed iff $Y^{c}:=X\setminus Y$ is open

## lemma 
Let $X$ be a topological space then for any collection $\set{A_{i}}_{i\in I}$ of closed sets we have 
1. if $|I|<\infty$ then $\bigcup\limits_{i\in I}A_{i}$ is closed
2. $\bigcap\limits_{i\in I}A_{i}$ is closed

### Proof of 1.
$(\bigcup\limits_{i\in I}A_{i})=((\bigcup\limits_{i\in I}A_{i})^{c})^{c}=(\bigcap\limits_{i\in I}A_{i}^{c})^{c}$

Since each $A_{i}$ is closed, $A_{i}^{c}$ is open and $I$ is finite so the finite intersection is open as well, taking its complement gives a closed set.

### Proof of 2.
$(\bigcap\limits_{i\in I}A_{i})=((\bigcap\limits_{i\in I}A_{i})^{c})^{c}=(\bigcup\limits_{i\in I}A_{i}^{c})^{c}$

again, $A_{i}$ is closed so $A_{i}^{c}$ is open so the union of opens is open, thus its complement is closed

## Def. closure
Let $A\subseteq X$ be a subset of a topological space $X$ , then
the closure of  $A$ is given by $\overline{A}:=\bigcap\limits_{C\supseteq A, C \text{closed}}C$ 

By the preceeding lemma, the closure is obviously closed since its an intersection of closed sets

## Theorem 1, characterization of closed
Let $A\subseteq X$ be a subset of a topological space $X$ , then
$A$ is closed iff $A=\overline{A}$ 

### Proof
We first prove the left right implication (=>) so suppose $A$ is closed, then $A$ is a closed set containing $A$ so
$A\supseteq A$ , $A$ is closed, by definition of the closure this impies $\overline{A} \subseteq A$ 

But any  of the sets $C$ forming the intersecton contain $A$ so we get
$\overline{A}=\bigcap\limits_{C \text{ closed},C\supseteq A}C\supseteq A$  , therefore we have 
$A\subseteq \overline{A}\subseteq A$ which gives us $A=\overline{A}$ 

Now lets proceed with the right left implication (<=)
Suppose we have $A=\overline{A}$ then

$\overline{A}=\bigcap\limits_{C \text{ is closed},C\supseteq A}C$ , by the preceeding lemma, an arbitrary intersection of closed sets is closed

so we are immediately done.
$\square$ 

## Def neigbourhood
Let $x\in X$ be a point in some topological space $X$ then the neighbourhood of $x$ is given by
$\mathcal{N}(x):= \set{U\text{ open}| x\in U}$ 


## Theorem 2, consistency with alternative definition
Let $A$ be a subset of a topological space $X$ then
$A$ is closed iff $\forall x\in X\setminus A \exists U\in \mathcal{N}(x): U\subseteq X\setminus A$ 

### Proof
(=>)
assume $A$ is closed, then
$A=\overline{A}=\bigcap\limits_{Z\supseteq A, Z\text{ closed}}Z$ 
which implies 
$A^{c}=\bigcup\limits_{Z\supseteq A, Z \text{ closed}}Z^{c}$ 
also notice that $Z\supseteq A$ implies $Z^{c}\subseteq A^{c}=X\setminus A$ 
Now let $x\in X\setminus A$ be some arbitrary point 
we now get from the preceeding lines
$x\in  \bigcup\limits_{Z\supseteq A, Z\text{ closed}}Z^{c}$ 
so there exists at least one $Z\supseteq A$ that is closed and $x\in Z^{c}$ 

Since $Z^{c}$ is open and $x\in Z^{c}$ this means that $Z^{c}\in \mathcal{N}(x)$ 

And given that $Z^{c}\subseteq A^{c}=X\setminus A$ , we are done with this direction.

(<=)
So suppose now that 
$\forall x \in X\setminus A \exists U_{x}\in \mathcal{N}(x): U_{x}\subseteq X\setminus A$ 

This defines a collection $\set{U_{x}}_{x\in X\setminus A}$ where we pick one neigbourhood per $x$, satisfying the preceeding statement

Its hard to escape the noticing that 
$A^{c}=X\setminus A=\bigcup\limits_{x\in X\setminus A}\set{x}\subseteq \bigcup\limits_{x\in X\setminus A} U_{x}\subseteq X\setminus A=A^{c}$   
where the first inclusion is given by the fact that there exists such a neighbourhood for each point in $X$ 
we conclude by recalling that the intersection of arbitrary closed sets, is closed which happens to be $(A^{c})^{c}=A$ 
$\square$

## lemma 3
Let $A$ be some subset of some topological space $X$
$x\in \overline{A}$ iff $\forall U\in \mathcal{N}(x):U\cap A\neq\emptyset$ 

### Proof
(=>)
Suppose $x\in \overline{A}$ , so by definiton of the closure for any closed set $Z$ with $Z\supseteq A$ we have 
$x\in Z$ 
Now suppose towards absurdity that 
$\exists U \in \mathcal{N}(x):U\cap A=\emptyset$ 
This implies $A\subseteq U^{c}$ ,since $U$ is open, $U^{c}$ is closed and it contains $A$ so we have
$x\in U^{c}$ but this is absurd since $x\in U$ which would imply that
$U^{c}\cap U\neq \emptyset$ 
So there cannot exist such $U$ which proofs that
$\forall U\in \mathcal{N}(x):U\cap A\neq \emptyset$ 

(<=)
Now we consider any point $x\in X$ that satisfies
$\forall U\in \mathcal{N}(x):U\cap A\neq \emptyset$ 
Now assume towards absurdity that there exists a closed set $C$ with $A\subseteq C$ and $x\not\in C$ 
This implies that $x\in C^{c}$ which is open and thus $C^{c}\in \mathcal{N}(x)$ 
So we have $C^{c}\cap A\neq \emptyset$ , but this cannot be true because
$A\subseteq C$ implies $A^{c}\supseteq C^{c}$ so $C^{c}\cap A=\emptyset$
this is absurd, so such a $C$ cannot exist, which means $x$ is a member of every such $C$ so
$\forall C\supseteq A,C\text{ is closed}:x\in C$ which implies 
$x\in \overline{A}$ and we are done
$\square$

## Def. Filter
A collection $\mathcal{F}$ of subsets of $X$ is called a filter iff
1. $X\in \mathcal{F}$ 
2. if $A\in \mathcal{F}$ and $A\subseteq B\subseteq X$ then $B\in \mathcal{F}$
3. if $A,B \in \mathcal{F}$ then $A\cap B \in \mathcal{F}$ 

A filter $\mathcal{F}$ is said to be proper iff $\emptyset \not\in \mathcal{F}$
## Theorem 4, bradley
Let $A$ be a subset of some topological space $X$ then
$x\in \overline{A}$ iff $\exists \mathcal{F}\text{ a proper filter}:\mathcal{N}(x)\subseteq \mathcal{F}, A\in \mathcal{F}$

### Proof
(=>)
suppose $x\in \overline{A}$ 
Define the filter base $B:=\set{U\cap A| U\subseteq X, U\in \mathcal{N}(x)}$
and the filter $\mathcal{F}=\set{D\subseteq X|\exists C \in B, C\subseteq D}$

Because $U\cap A\subseteq X$ and $U\cap A \in B$ we have $X\in \mathcal{F}$ satisfying the first property of a filter

Now suppose that $Z\in \mathcal{F}$ then any superset $Z'\supseteq Z$ that is also a subset of $X$ , is in the filter because
$\exists (U\cap A)\in B: U\cap A \subseteq Z$ and therefore we have 
$U\cap A \subseteq Z \subseteq Z'$ which implies $Z'\in \mathcal{F}$ 
which proves the second property of a filter

Lastly, consider $Z_{1},Z_{2}\in \mathcal{F}$ we aim to show $Z_{1}\cap Z_{2}\in \mathcal{F}$ 
Its clear that $\exists U_{1},U_{2}\in \mathcal{N}(x)$ with 
$U_{1}\cap A \subseteq Z_{1}$ and 
$U_{2}\cap A \subseteq Z_{2}$  which gives
$U_{1}\cap A \cap U_{2}\cap A$
$=U_{1}\cap U_{2} \cap A\subseteq Z_{1}\cap Z_{2}$ 
where $U_{1}\cap U_{2}\in \mathcal{N}(x)$ because finite intersections of opens is open and both contain $x$ by def.
so therefore $U_{1}\cap U_{2} \cap A \in B$ 
which means that $Z_{1}\cap Z_{2}\in \mathcal{F}$ 
which proves tha $\mathcal{F}$ is indeed a filter

Now recall from lemma 3 that because $x\in \overline{A}$ we have 
$\forall U\in \mathcal{N}(x):U\cap A\neq \emptyset$ 

So for any superset $Z\supseteq U\cap A$ we conclude 
$Z\neq \emptyset$ which shows that the filter is proper

Lastly, because of $U\cap A\subseteq A$ we have $A\in \mathcal{F}$ but also 
$\forall U\in \mathcal{N}(x):U\cap A\subseteq U$ which implies 
$\mathcal{N}(x)\subseteq \mathcal{F}$ which shows that the filter 'converges' to $x$
this concludes this direction of the proof

(<=)
Let $x\in X$ be some point and let $\mathcal{F}$ be a proper filter satisfying the assumptions, that is 
$\mathcal{N}(x)\subseteq \mathcal{F}$ and $A\in \mathcal{F}$ 
by the third property of any filter we have for any $U\in \mathcal{N}(x)$
$U\cap A \in \mathcal{F}$ 
since the filter is proper $U\cap A\neq \emptyset$ 
by lemma 3 we get $x\in \overline{A}$ which concludes this proof
$\square$

