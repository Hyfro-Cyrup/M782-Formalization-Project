# M782-Formalization-Project
Type theory formaliztion project using a proof assistant. Unsure if LEAN is better than Agda, but went ahead and converted my whole repository into a LEAN project though because LEAN doesn't know the difference between a project and a repo. 

## My Topic
My plan is to formalize categorical limits into type theory. The current end goal is to prove the theorem that if a category has all (finite) products and equalizers, then it has all finite limits. 
I will start with formalizing categories and functors, then work my way up. I'm unsure how well the scope of this projects aligns with expectations. Will talk to instructor about it. 

## Current Questions
Two things about the agda standard library since familiarization is a goal. 
1. There's surely some builtin record that does exactly what I want from `ProofIrrelevantSubtype`. Can I have some help finding it?
2. In `Limits.agda`, I define the proposition `has-unique-term` to mean isomorphic to the unit type. I'm more okay with this not being builtin because it feels like different data than an isomorphism. If there's some variant of `is-contractible`, though, that would probably slot in well here. 

One thing about your opinion
3. You seem to prefer Agda over Lean, and I'm curious to hear why. For me, Agda seems to come much more naturally and enjoyably and I can't put my finger on why. I do think I sacrifice some readability though, which is fine. 
