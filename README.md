# M782-Formalization-Project
Type theory formaliztion project using a proof assistant. Unsure if LEAN is better than Agda, but went ahead and converted my whole repository into a LEAN project though because LEAN doesn't know the difference between a project and a repo. 

## My Topic
My plan is to formalize categorical limits into type theory. The current end goal is to prove the theorem that if a category has all (finite) products and equalizers, then it has all finite limits. 
I will start with formalizing categories and functors, then work my way up. I'm unsure how well the scope of this projects aligns with expectations. Will talk to instructor about it. 

## Initial Brainstorming
A category is a collection of objects (type? class?) with a function Hom : Obj -> Obj -> Class and a function Comp : (A, B, C) -> Hom(A, B) -> Hom(B, C) -> Hom(A, C) such that axioms. 
I wonder how best to encode "such that axioms". It's surely incredibly common, so I'll find an example soon whether I seek it out or not. My first guess is that for each axiom, the data of a category should contain an element of the proposition-as-type representing the axiom.

A functor is two functions such that axioms. 
