- [x] Make everything compile again.
- [x] Define two logics, oProp and iProp
- [x] Define the modality
- [x] Define lemma's for the modality
- [x] Write down own_** lemma's
- [x] Write lemma's for owned and ∗, ∃, emp, mono, persistently
- [x] Fix htypesystem.v to use iProp/oProp
- [x] Prove the owned lemma's

- [ ] Prove the own_** lemma's, modulo acyclicity
- [ ] Multiset trees
- [ ] Make proofmode work with owned
- [ ] Fix preservation.v to use iProp/oProp as appropriate
- [ ] Figure out adequacy statement for deadlock and leak freedom
- [ ] Prove deadlock and leak freedom
- [ ] Recursive types
- [ ] Write ICFP paper


Abstract
========

Situation: working >1 year on this problem, still no paper.
My view: things are not going well; the probability that I will work on it for another year and still not have a paper is non-negligible.

I want to diagnose the problem and find a solution. Basically: what can I do to fix this?


High level goal
===============

Taking a step back, what is our high level goal?

My high level goal: do a succesful PhD so that I have a shot at continuing in academia.

This involves, as far as I can tell:
- First and foremost, publishing X number of papers.
- Teaching.
- Developing skills (presenting, writing, Coq, TikZ, talking to people,...).
- Collaborations and getting to know people in the field.
- Going to conferences / research visits.
- Writing grants.
- First point is by far the most important

Your level goal: ...? (I think our goals are more or less aligned, but I'd still like to know...)

Point being, it's probably important for both of us to try and maximize X.
So maybe it's good to take a step back and figure out a strategy for doing that.
Even if it turns out our current approach is more or less optimal, it may still pay off because when I have a clear idea why I'm doing what I'm doing, it increases my motivation.


Diagnosis
=========

Can you help me diagnose the problem?

My partial diagnosis of the problem: (1) approach (2) motivation.

Motivating, for me, is:

1) Mathematically beautiful work
2) Interesting/powerful theorem
3) Interesting puzzles
4) Useful work (in a broad sense)
5) Others interested in the work
6) Seeing a path to a finished paper
7) Lasting impact

Current main approach: just do Coq hacking.

We started modifying heaplang with WAS, changing Iris WP, etc. All that time was, basically, wasted, exept insofar as I learned a bit about how Iris works. Last week I spent writing hlogic.v. Hearing that it most likely needs to be deleted is demotivating. Maybe it's still useful in order to obtain insights, but I'm not sure it's an efficient way to do that: 99% of the time I'm stuck on silly problems, which don't bring any insight.

Current situation is almost an inverse of 1-7:

1) The proofs are ugly -- maybe this is inherent in the work, since lambda calculus + session types + buffers is a human invented system, so why expect proofs about it to be nice?
2) The theorem we're trying to prove is trivially true. We know it's true and we know why. The only difficulty is convincing Coq.
3) The puzzles are, most of the time, uninteresting: Coq technical issues, and even the more high level issues are not all that interesting.
4) The work doesn't seem like it will ever be useful in practice, but reasoning about deadlocks in separation logic seems like an okay research goal, of which we are now doing a special case.
5) I don't see how anyone else will be interested in it. The reviewers will read the paper, basically.
6) I don't currently see a path to a finished paper. We're stuck.
7) Maybe a fully general way to reason about deadlocks in separation logic will have lasting impact, but this special case will only have that insofar as it is the start of that.

Result: forcing myself to stare at the screen while trying to prove another lemma, then contemplating (1-7). Not thinking about the problem much outside of that. Very little creativity.



