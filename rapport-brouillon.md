# Rapport TAAS

Auteur: Aboubacar DIAWARA (21213801)
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
{ N \space(n):Nat}
\quad (Entier)\]

## 2. Operations mathématiques

\[
\frac{\Gamma \vdash n1:Nat \quad \Gamma \vdash n1:Nat}
{ Gamma \vdash Add(n1, \space n2):Nat}
\quad (Addition)\]

\[
\frac{\Gamma \vdash n1:Nat \quad \Gamma \vdash n1:Nat}
{ \Gamma \vdash Sub(n1, \space n2):Nat}
\quad (Soustraction)\]

## 4. Abstraction

\[
\frac{\Gamma \vdash x:\tau_1 \quad \Gamma \vdash b:\tau_2}
{ \Gamma \vdash Abs(x, \space b):\tau_1\rarr\tau_2}
\quad (Abstraction)\]

## 6. Application

\[
\frac{\Gamma \vdash f:\tau_1\rarr\tau_2 \quad \Gamma \vdash e:\tau_1}
{ \Gamma \vdash App(f, \space e):\tau_2}
\quad (Abstraction)\]

## 6. Liste

\[
\frac{\Gamma \vdash x:\tau \quad \Gamma \vdash xs:PList \space (\tau)}
{ \Gamma \vdash Cons \space (x,\space xs) : PList \space (\tau) }
\quad (Liste \space native)\]

\[
\frac{\Gamma \vdash l : (PList \space \tau)}
{ \Gamma \vdash Head \space l : \tau }
\quad (Primitive \space head)\]

\[
\frac{\Gamma \vdash l : (PList \space \tau)}
{ \Gamma \vdash Tail \space l : (PList \space \tau) }
\quad (Primitive \space Tail)\]

## 7. Conditions

\[
\frac{\Gamma \vdash l : (PList \space \sigma) \space \Gamma \vdash e1 : \tau \space \Gamma \vdash e2 : \tau}
{ \Gamma \vdash IfEmpty \space (l, e1, e2) : \tau }
\quad (IfEmpty \space Liste)\]

\[
\frac{\Gamma \vdash n : Nat \space \Gamma \vdash e1 : \tau \space \Gamma \vdash e2 : \tau}
{ \Gamma \vdash IfZero \space (n, e1, e2) : \tau }
\quad (IfZero \space nat)\]

## 8. Let
\[
\frac{\Gamma \vdash e1 : \tau1 \quad \Gamma \vdash e2 : \tau2}
{ \Gamma \vdash Let \space (x, \space e1, \space e2) : (TRef \space \tau) }
\quad (Let)\]

## 9.Traits imperatifs

\[
\frac{\Gamma \vdash e : \tau}
{ \Gamma \vdash Ref \space e : (TRef \space \tau) }
\quad (Ref)\]

\[
\frac{\Gamma \vdash e : (Ref \space \tau)}
{ \Gamma \vdash Bang \space e : \tau }
\quad (Bang)\]

\[
\frac{\Gamma \vdash e1 : (TRef \space \tau_1) \space e2 : \tau_1}
{ \Gamma \vdash Mut \space (e1, e2) : TUnit }
\quad (Mutation)\]

\[
\frac{\Gamma \vdash x_i : \tau_i}
{ \Gamma \vdash Sequence \space (x1, \space ...Sequence(x2, \space Sequence(xn, []))) : x_n }
\quad (Sequence)\]

# Evaluation

## 1. Valeurs finales

Les seules valeurs finales sont des entiers. Aucune étape d'evaluation supllémentaire ne peut être effectuée. Cel

## 2. Valeurs intermediaires

Les autres valeurs peuvent toujours subir au moins une étape d'évaluer. Dans cette section je vais presenter les règles d'évluation des autres traits.

### 2.1 Conditon sur les entiers et les listes
J'evalue d'abord la condition, ensuite suivant la valeur entière correspondante, je choisi d'evaluer uniquement la branche appropriée. Même strategie pour la liste.

### Sequence d'instructions
J'evalue de façons sequentielle chaque instruction. L'environnement fournie par l'instruction *i* est l'environnement d'evaluation de l'instruction *i+1*. Le resultat de la sequence d'instruction est celui de la dernière instruction. Si la sequence est vide j'ai choisi de retouner *unit* comme resultat.



