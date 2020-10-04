# Linear Algebra Done Right in Coq: The First 24 Hours

I decided to formalize Linear Algebra Done Right (LADR) in Coq, though I'm having reservations about the choice of Coq. I stream this project 2-5p (frequently well past 5) eastern time every Sunday. I hope you follow me on [twitch](https://twitch.tv/quinndougherty92)! I also persist the videos to a [youtube playlist](https://www.youtube.com/playlist?list=PLGZRl2vU826d_IRnxA6rgTXXAG5vdx74P) and the code is available on [github](https://github.com/quinn-dougherty/ladr).

A friend convinced me to write a blog post every 24 hours of stream. This is the first such post. 

## The story so far. 

I thought about writing in "we" tense because it honestly feels like a collaboration, I especially want to single out twitch users gerhardgentzen, defl8, and soobtoob for their contributions. However, not every audience member is there all the time, and I'm still driving the thing, so "we" didn't quite fit for this 24 hour window, so I'll write in the "I" tense.

Chapter one of LADR is about vector spaces. Vector spaces are defined over their underlying fields, so I knew that the very beginning of the project would deal with field theories. A field is a ring with division satisfying certain laws. A ring is a one and a zero with a way of adding, subtracting, and multiplying satisfying some laws. There is excellent machinery for adding rings and fields to Coq, meaning you can use built-in tactics to manipulate and solve goals involving your home-rolled ring or field. 

I wanted this on stream, but I wanted slightly more: I also wanted the fact that something is a field to be a premise for forming a vector space. To do this, I used the machinery familiar to functional programmers as _typeclasses_, which are offered in Coq. 

Coq standard library defines a field theory _Record_ which is a syntax sugar around an _inductively defined proposition_. In short, a field theory is a proposition that the given type, functions, and constants satisfy the _field laws_. (The same is done with rings). I wanted to copy this pattern, so I spat out `vectorspace_theory` first as a `Definition` because I just wanted to create the proposition, then in ep 4 I changed it to `Record` to match the pattern in the standard library better. 

What the standard library does not do, however, is make field theory a term in a typeclass. There's a library called math-classes that's a bit closer to this, but I haven't explored it much. 

I wanted to work with typeclasses, however, because I want to inherit lemmas about vectorspace arithmetic and algebra every time I declare that something is a vectorspace. For example, if I worked with the type of length-indexed list (known as `t` in `Coq.Vectors` in standard library), none of my progress would help me if I then switched to functions `bool -> R`, which also form a vector space.

One of the things I learned from starting some proofs in specific vectorspace instances, and then going on to focus on proofs at the typeclass-level, is that proving stuff at the typeclass level isn't especially harder than proving stuff at instance level. I.e., you might as well prove it at typeclass level! 

After getting through section 1.A of the book (fields) and 1.B (vector spaces) and completing _most_ of the proofs (leaving `Admitted` peppered through the file, a reminder to come back and finish later), I decided to read ahead to section 1.C, on subspaces. I've made no decisions about how to formalize this yet, though I expect to use `Ensembles` (functions `V -> Prop`, a way of representing sets in type theory) and `Record`. The last 6 hours of this particular interval of 24 have been doing the exercises pen and paper. Yes, I will be taking hiati from writing coq to do pen and paper exercises. I should probably mention my math level: it is approximately the level such that it took me 6 hours to do the about 21 of the 24 exercises in section 1.C sans formalization. At linear algebra in particular, I have at least the literacy of an engineering major or data scientist, and I'm currently tutoring for a basic linear algebra section at a college. 

Something I learned in the last few hours of this interval of 24 is that direct sums are difficult to work with and I do not enjoy working with them. I anticipate great difficulty in formalizing them. 

## Questions going into the next 24 hours. 

1. Setoids. wtf. Like if you read the code you can see that I've started to use them, but there's so much more to understand about them. I hope this rabbit hole ~~doesn't~~ leads me all the way to SSReflect.
2. The ring theory obliges one to supply an equality operator (`R -> R -> Prop`) at runtime and the ring laws are described in terms of _that_ equality operator. However, when you're using rings in the arena the ring laws and everything else are done with Coq's basic `eq`. I want to understand how this is achieved. I know it has something to do with setoids. 
3. Tactics. Powerful tactics such that simply typing `vectorspace` can solve goals involving applications and rewrites of the vectorspace laws. 
4. Your coq session maintains a _database_ of rings and fields, which you can update by typing `Add Field my_field` (provided that you have the proof of the laws handy!) (note, this is what unlocks the power of field tactics for user-defined fields). It would be awesome to wire up a table of vectorspaces, so that I could type `Add VectorSpace myvspace` someday. This might involve OCaml, I really have no idea. I haven't spent time on zulip or discourse (which I'm told are the major Coq hubs) discussing this, because I haven't been working on this project off stream and and hasn't occurred to me to just go on zulip or discourse on stream. 
5. Really excited for span, independence, and bases (chapter 2) but it will have to wait until I formalize 1.C which includes sums and direct sums. This formalization part could take as much as the whole next 24 hours! I really don't know! 
6. This is complicated but I'm considered significantly derailing the stream's progress through the book to explore other proof assistants. Lean seems like a great choice, and any excuse is a good excuse to explore agda and I might try to shoehorn cubical in just for fun (not _just_ for fun like I'm having a lot of equality issues and for all I know cubical might help). 

## Final remarks for today

When I had this crackpot idea I ballparked a year. I could be wrong by a factor of 3. But the idea is I only actually _committed_ 3 hours on sunday, so it's not the end of the world if it takes longer than planned. It's possible that someday I'll have more time and work on it more than just sundays, too, but for now it's just 3 hours on sunday. 

I'd like to thank the following books
- Logical Foundations by Pierce et. al., which is the ultimate gateway into coq
- Verified Quantum Computing by Rand, which taught me rings and fields and empowered me to tackle parts of real analysis in coq, which is part of why I was able to do this project. 
- Linear Algebra Done Right by Axler, obviously. 

