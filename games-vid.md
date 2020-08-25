# Who wins in chess (and why all finite games are determined)?

## Introduction

"Who wins in chess?"

I mean, not who wins in a particular game of chess, or between two particular players, but like, if both players were *perfect*, who would win?
Note that I don't just mean "really good"---actually *perfect*.

## What are games?

Okay, like any question, if we want to provide a good (i.e., for the purposes of this video, logical) answer to the question, we need to make it clear what we're actually saying first.
What *is* a game?

One answer is the Wittgenstein-ian answer: "a game is anything that people call a game."

So chess is a game because people would call it a game.
And sure...that's true, and if we were trying to categorize actual games that people play, an approach adhering to this principle might answer the question of "what is a game?" by surveying a ton of people and collecting all the answers.

But we need to think about why we're actually asking question in the first place: because we want to talk *about* games in general.
What is actually helpful for our purposes are the questions "what are the properties of games?" and "what are all *possible* games?"
At first, this probably seems like a much more difficult question to answer.
But a good principle of math is that definition by property is an extremely powerful method for solving problems.
Asking how things behave instead of what they are will open up avenues of attack.

So what are games, in a mathematical sense?

Well, we're trying to answer questions about chess and other "chess-like" games, so let's think about chess and what properties it has.
More importantly, let's think about the original question we asked: "who wins in chess?"
What does it even mean for someone to "always win" a game?

One interpretation, that we will be using in this video, is that no matter what the other player does, it's possible to "counter" their move somehow.
More precisely, there's some "instructions" that say "when your opponent does X, do Y", which is completely unambiguous: for each possible thing your opponent can do, it lists a single action that you can take.
Something to note is that there may be multiple actions that would lead to a victory; but that doesn't actually change anything---we can just pick one of these actions and write it down in the manual.

Then for someone to win this game, all we have to do is give them the manual, which tells them exactly what to do for the entire game.
Such a "manual" actually literally exists for some games, like Tic-Tac-Toe (see XKCD).

The question we're trying to answer then is: could there be such a manual for chess (or games like chess)?
This question is still a bit non-rigorous, so let's pin it down, first by establishing what we mean by a game that's "like chess."

Let's list some features of chess.
But first, pause the video for a minute, and think of some properties of chess that seem important.
For example, one property that will be important is that there's no randomness; on the other hand, it's probably not going to matter that the two colors typically used for the pieces are black and white, the answer would be the same if the colors were red and green, for example.

**PAUSE**

Here's a list of some important features.
Don't worry if you didn't think of all of them.

1. There's no randomness.
2. Players move in a well-defined sequence in distinct rounds.
3. Each player has a predetermined set of moves they can play at each round.
4. It's a "perfect-information" game.
5. After the game is over, there's a winner and a loser.

A lot of times math classes present math as though it all came into existence at once, but it's important to remember that mathematicians, lots of very smart people, have thoughts about these problems for hundreds or even thousands of years, sometimes spending their entire lives on problems that you learn the solutions to in a single day.
We've arrived at this definition of game after lots of thought, and if you thought of a characteristic that's not on the list, you may not even be "wrong"!
It could be that your characteristic is also a mathematically interesting answer to the question, "what is a game?"

But in this video, we'll focus on the widely-used definition of game that we'll get to in a moment.
But first, let's talk about why we want these characteristics.

The main characteristic we care about is that we want to be able to know the current state of the game given only the moves that have been played so far.
This is so that we can have a hypothetical "manual" which tells the player what to do.

1. There's no randomness.
    - This is important, because if there was randomness, there'd be no hope of having such a manual.
    - For example, let's say the game we're playing is the following: we roll two dice, and we both guess what the sum of the two dice will be.
        - There's no strategy that will **guarantee** that we win (without rigging the game or something).
        - We can improve our chances of winning by knowledge of probability, but that's not the same.
2. Players move in a well-defined sequence in distinct rounds.
    - If this weren't the case, say two players could move at the same time, then there's also no way to
3. Each player has a predetermined set of moves they can play at each round.
    - This is important because it means that the manual can actually have all the possible moves of the opponent.
4. It's a "perfect-information" game.
    - In our case, this means that both players can see the whole board, or more rigorously, that we can determine the state of the game only by knowing the sequence of moves played so far.
    - Otherwise, the manual couldn't account for every possible move of the opponent, because there's no way of knowing what the moves they can make even are.
5. After the game is over, there's a winner and a loser.
    - This is important because it's meangingless to have a manual that tells you how to a win a game that doesn't have a winner.
    - You might consider this so obvious it doesn't need any mention, but for our definition to be rigorous, we need to account for everything.

Note that even though this list of characteristics is reasonably precise, it's not yet a rigorous definition.
That comes next.

### Solved games vs. not solved games

### Which one is chess?

### Can we even answer the question?

So we don't know which one chess is...but maybe it's neither?
Do all deterministic games have a fixed outcome for perfect players?

This question will lead us down a rabbit hole of logic, which touches on the foundations of mathematics.
But first, let's talk about some simpler kinds of games.

## Finite games

Notably, it doesn't matter how **many** moves there are, but how many times you can make a move.
Although if there are infinitely many moves, you may not be able to actually **compute** the winning strategy, but it still, in some sense, exists (though some people may reasonably disagree with this use of the word "exist").

## The proof

This is a going to be a proof by contradiction.
We'll take some arbitrary finite game and show that it must be determined: that is, there must be some strategy.
Let's say we have a finite game whose tree looks like this (SHOW TREE), and we'll highlight all the winning positions for player 1, so the winning positions for player 2 are every other ending configuration.

Now, suppose that the game **isn't** determined: there's no way for **either** player to guarnatee that they always win.

We'll actually make a new definition now, so that we can talk about things more easily.
This is often a useful thing to do so that proofs are more understandable.
We'll say that a position is a "winning position for X" if player X has a winning strategy **starting from that position**.
Then when we say a game is "determined", what we mean is that the first position is a winning position for either player 1 or player 2.

So if the game is **not** determined, that means that the first position is not a winning positio either player.

Now let's consider the first move, made by player 1.
No matter what they do, every move must lead to a position which is not a winning position for player 1.
This is because we assumed that the first position is not a winning position for player 1: if player 1 could make a single move that guaranteed them a win, then the original position would also be a guaranteed win for them, because they get to choose the first move.

But some of these positions may be winning positions for player 2.
However, they can't **all** be winning positions for player 2: if they were, then it doesn't matter what player 1 does, because player 2 is guaranteed to win!
And that would mean that player 2 is actually guaranteed to win the game, which we assumed was not the case.
So there has to be some move that player 1 can make which does not guarantee a win for player 2, so player 1, being perfect, would choose one of those.

Now let's consider the second move, made by player 2.

## Chess isn't technically like this, but basically tho

## Discussions

### Possibility vs. Optimization Questions

There are many ways to split up questions, but one of the ways I like to split up problems is this: is the question asking if something is **possible**, or is it asking for an optimization?
Probably not all problems fit well into this, but I'm the most interested in problems in the first class.
Notably, this video explores the question of "is there someone always wins in chess, or do we always tie?" is a possibility problem, in the sense that we know it has an answer (specifically, "yes"?)

### Unsolvable vs. Provable vs. Computable vs. "Practically Computable"

REED: PROBABLY CUT THIS

There are many ways to split up questions, but I like to split up problems like this.
First, some problems have provable solutions, and some don't.
For example, the Continuum Hypothesis is famously a problem which has no solution, and in the case of the Continuum Hypothesis, it's because there's not enough information to answer the question in the first place.
It's like if I asked the question "suppose n is 3k + 1 for some integer k, is n even or odd?"
You'd reasonably say something like, "well it could be, or it could not be, but I need more information" (e.g., "what's k?").
Maybe I'll make another video about that, but the short of it is that there's no proof of the Continuum Hypothesis **or** the negation of the Continuum Hypothesis.

This is very different from other questions, which have definite proofs of truth or falsehood.
We're much more used to questions that have provable answers, because that's the easiest thing to wrap our heads around: "is 4 even" is a question that has a provable answer.
Among the questions that do have provable answers, there are still several subsets of these questions:
1. Those with provable answers (i.e., all of them)
2. Those with computable answers (i.e., decidable problems)
3. "Practically computable" questions: questions whose answer is not only computable, but within some "reasonable" amount of time (e.g., a lifetime).

### Rant about categorization

Side-note: I would like to point out that this is a *well-defined* categorization.
It's fairly common to classify things into groups to understand them, but a lot of the time the groups are not actually well-defined: there's no rigorous definition of what diferentiates each group, just vague definitions.
That's okay, sometimes, but it needs to be acknowledged.

## Borel Determinacy?

## The axiom of determinacy?

