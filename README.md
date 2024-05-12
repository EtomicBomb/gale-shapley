# Exploring the Gale–Shapley Algorithm

Collaborators: Ethan Williams(ewilli51), Enock Nyakundi(enyakundi), Muhiim Ali(mali37)

Demo Video (~ 2 mins): https://youtu.be/VvZgK1gxtIQ

# Project Overview

This project is an exploration of the Gale-Shapley algorithm. It comes with:

- A formal description of stable matching
- A formal description of the Gale-Shapley algorithm
- Experiments regarding Gale-Shapley for checking properties of the algorithm
- A visualizer for the above

This project is written in <a href="https://csci1710.github.io/forge-documentation/home.html">Forge</a>, which is a modeling language similar to Alloy.

# Introduction

In the stable matching problem, several participants rank their preferences over other participants. The goal is to find a matching of participants that is stable: one where no pair of participants would rather be with each other than their assigned matches.

There are several variants of the stable matching problem. We have chosen to consider the variant where the participants are divided into two disjoint sets, called proposers and receivers. Proposers rank their preferences over receivers, and receivers rank their preferences over proposers. We allow proposers and receivers to leave some participants unranked; particpants are only be matched with participants they have ranked. A matching is a set of pairs of proposers and receivers. Each participant may have one or no matches.

An application for this version of the stable matching problem could be matching mentors and mentees.

# Model Design and Visualization

## Model Design

Most descriptions of the Gale-Shapley algorithm are implementation-focused. In this way, they contain extra data structures that serve as redundant indexes into other data structures. These help with runtime performance. To model the algorithm in Forge, it was beneficial to find a minimal description of the Gale-Shapley algorithm.

The state of the algorithm in our model is represented by one data structure, `offer`. It is a set of pairs of proposers and receivers. A proposer-receiver pair `(px, rx)` means that `px` is proposing to `rx` in that round; _or_ that `px` already has a tentative match to `rx`. The pair `(px, rx)` is considered a tentative match if `rx` accepts the proposal: if `px` is the only proposer matched with `rx` and `rx` ranks `px`. By lumping together tentative matches and active proposals, we are able to unify the two kinds of rejections in Gale-Shapley: receivers leaving proposers for a more favorable match, and proposers proposing to receivers where the receiver does not rank the proposer.

The initial state of `offer` has every proposer paired with their favorite receiver. We have a non-standard termination condition: all of the pairs in `offer` are tentative matches. In other words, each receiver has exactly one entry in `offer`, and the corresponding proposer is one that they rank.

Other descriptions of the algorithm involve modifying an explicit collection of tentative matches. By avoiding this and using this simplified description of the algorithm, our tests become simpler and more performant.

Our code also supports multiple sets of preferences for the participants. This is so that we can run multiple instances of the algorithm in parallel, and observe how changing the preferences influences the resulting match.

Developing this representation took significant effort, so we tried several other ways of representing the step-by-step nature of the algorithm. At one point we had two other data structures in `Status`.

## Tradeoffs

We only were able to choose one variant of the stable matching algorithm. We were able to run multiple instances of the stable matching algorithm at once. There were no experiments that are not included in the final report since we basically made linear progress.

## Assumptions About Scope

Aside from choosing one variant of the stable matching algorithm, we are also assuming that each receiver and proposer represent a single party, and that they are able to encode their preferences in a rank list.

## Goals Change Since Proposal

We met all of our target goals. We did not get to some of the reach goals, like considering other variants of the algorithm, nor did we develop a custom web interface (other than the one that comes with Sterling). We did not address lack of information either.

## How to Understand The Visualizer

The visualizer, `model_vis.js` shows a single step in the algorithm. You can use the time buttons to advance to the next step. The final step is the resulting match. Temporal Forge will loop back around to the final step as the lasso.

The different columns correspond to multiple executions of the algorithm.

The preferences, the proposer and receivers, and the offer status which changes over time are also shown.

## Visualization

Since the default visualizer is hard to read, we created a custom visualizer for our model in `model.vis.js`. To run the visualizer, run model.frg using either the green button or run it through the terminal by typing `racket model.frg`. Unfortunetly, the visualizer doesn't load automatically, so you have to go to the Script section in the Sterling visualizer, copy the script in `model.vis.js`, and paste it into the script section. Make sure to run it through the svg option.
When you run the custom visualizer, you'll see multiple grids representing the proposer's and receiver's true and false preferences. The grids below these show the offers from proposers to receivers at different stages.

# Signatures

1. **Receiver**  
   Represents the receivers in the matching process.

2. **Proposer**  
   Represents the proposers in the matching process.

3. **RxPref**  
   A partial function that maps proposers to an integer, indicating preferences from the receiver's perspective.

4. **PxPref**  
   A partial function that maps receivers to an integer, indicating preferences from the proposer's perspective.
5. **Status**  
   Represents the offers from proposers to receivers at any given time. The offers in the final state represent the matches.
6. **PxPrefs**  
   A partial function mapping proposers to their preference lists.

7. **RxPrefs**  
   A partial function mapping receivers to their preference lists.

8. **Matching**  
   A partial function mapping proposers to receivers, representing the current state of matches.

# Project Structure

## `model.frg`

This file contains a formal specification of the stable matching property:
=> For a matching to be considered a stable match it has to satisfy these two requirements:

1.  individual rationality: a matching is individually rational if nobody would strictly prefer to not to match than staying with the partner prescribed by the matching.
2.  absence of blocking pairs: A pair (px, rx) is called a blocking pair for a matching if both px and rx prefer each other more than their current match

It also contains a formal specification of the Gale-Shapley algorithm.

## `model.tests.frg`

This includes tests of our model. These tests are included to make sure that our model is correct.

## `model.experiment.frg`

This includes statements that check specific properties of the Gale-Shapley algorithm.

## `model.demo.frg`

This includes the run statements for our presentation and video.

## `model_vis.js`

A visualizer for running our model and seeing the resulting offers.

## `matching_vis.js`

A visualizer for seeing what matches look like.

## `README.md`

You are here.

# What We Learned

We wanted to see if there are stable matchings that cannot be produced by the Gale-Shapley algorithm. We found out that this is the case, since there are some sets of preferences for which there exist multiple stable matchings. The Gale-Shapley algorithm is fully deterministic.

We wanted to see if lying can benefit proposers. We verified that, with three or fewer participants, a proposer that misrepresents their individual preferences can never benefit.

We wanted to see if lying can benefit receivers. In fact it is possible that a receiver can misrepresent their true preferences and get a better outcome.

We wanted to see if colluding can benefit proposers. If two proposers misrepresent their preferences, they will not both benefit. However we found out that two proposers can misrepresent their preferences, allowing one to benefit.

We wanted to see if colluding can benefit receivers. This is possible, as a consequence of the fact that one receiver can misrepresent their preferences and benefit.

Proposer-receiver collusion is possible in that if a proposer and a receiver coordinate to misrepresent their preferences, they cannot both benefit, but either single member of the pair can.

These properties of the algorithm were previously well known, but we verified them using Forge and without any domain-specific mathematical techniques.

These properties have major implications for implementers of the Gale-Shapley algorithm. In particular, effort to prevent misrepresentations by receivers are absolutely required. These measures may include discovering the true preferences from means other than asking receivers to self-report them.

Additionally, effort is required for ensuring that proposers do not collude. This may include only using the Gale-Shapley algorithm in places where there are no strong outside motivations. Since colluding between proposers is only beneficial if one proposer gets a worse outcome, it could also be advisable to only admit proposers who are motivated to get the best outcomes.

# Collaboration

We did not receive outside help on this assignment.
