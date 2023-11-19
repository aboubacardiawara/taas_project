# Rapport TAAS

Implementation d'un mini langage typé

# Introduction

Implementation d'un evaluateur et d'un typeur.

# Elements du langage

## Ce qui est fait

- Entier naturel
- Fonction lambda (Abstraction)
- Application de fonctions
- Operations mathématiques
  - Addition
  - Soustraction
  - Multiplication
- Liste native
- Condition
  - Sur les listes
  - Sur les entiers
- Liaison (Let)
- Traits imperatif
  - Reference
  - Dereferencement
  - Mutation
  - Sequence d'instructions

## Ce qui n'est pas fait

- Le point fixe
- Polymorphe faible
- Aller plus loin

# Quelques traits

Dans cette section, je presente quelques éléments importants de mon implementation. Plus précisement, leur sémantique et les règles de typage associées.

# Typage

\[
Var(string)∣Arr(ptype,ptype)∣Nat∣PList(ptype)∣TPunit∣TRef(ptype)∣Forall(string list,ptype)
\]

## 1. Entier

\[
\frac{}
{ env \vdash Nat\space(n):Nat}
\quad (Entier)\]

## 2. Operations mathématiques

\[
\frac{env \vdash n1:Nat \quad env \vdash n1:Nat}
{ env \vdash Add(n1, \space n2):Nat}
\quad (Addition)\]

\[
\frac{env \vdash n1:Nat \quad env \vdash n1:Nat}
{ env \vdash Sub(n1, \space n2):Nat}
\quad (Soustraction)\]

## 5. 
## 4. Liste

\[
\frac{env \vdash x:\tau \quad env \vdash xs:PList \space (\tau)}
{ env \vdash Cons \space (x,\space xs) : PList \space (\tau) }
\quad (Liste \space native)\]

\[
\frac{env \vdash l : (PList \space \tau)}
{ env \vdash Head \space l : \tau }
\quad (Primitive \space head)\]

\[
\frac{env \vdash l : (PList \space \tau)}
{ env \vdash Tail \space l : (PList \space \tau) }
\quad (Primitive \space Tail)\]

# Evaluation

## 1. Valeurs finales

Les seules valeurs finales sont des entiers. Aucune étape d'evaluation supllémentaire ne peut être effectuée.

## 2. Valeurs evaluables

Les autres valeurs peuvent toujours subir au moins une étape d'évaluer. Dans cette section je vais presenter les règles d'évluation des autres traits.

### 2.1
