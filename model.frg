#lang forge/temporal
option max_tracelength 10
option run_sterling "model_vis.js"

sig Receiver {
    rx_pref: pfunc Proposer -> Int // Receivers rank Proposers
}

sig Proposer {
    px_pref: pfunc Receiver -> Int // Proposers rank Receivers
}

-- TODO: create new sigs ReceiverPreferences and ProposerPreferences,
-- which are paramaters for stable*[] predicates
-- then, we can alter these to see the impact on the resulting matches?
-- note: pfunc constraint cannot be expressed: illegal syntax: Receiver -> pfunc Proposer -> Int

// ordered preferences, with the numbers 1 to n
pred wellformed_px_pref[px: Proposer] {
    px.px_pref[Receiver] = { i: Int | 0 <= i and i < #{px.px_pref} }
}

// ordered preferences, with the numbers 1 to n
pred wellformed_rx_pref[rx: Receiver] {
    rx.rx_pref[Proposer] = { i: Int | 0 <= i and i < #{rx.rx_pref} }
}

pred well_formed_preferences {
    all px: Proposer | wellformed_px_pref[px]
    all rx: Receiver | wellformed_rx_pref[rx]
}

sig Matching {
    matching: pfunc Proposer -> Receiver
}

// matching is bijective, but may exclude some Proposers or Receivers
pred wellformed_matching[m: Matching] {
    all rx: Receiver | lone m.matching.rx
}

pred wellformed_matching_px_pref_rx_pref {
    all m: Matching | wellformed_matching[m]
    all px: Proposer | wellformed_px_pref[px]
    all rx: Receiver | wellformed_rx_pref[rx]
}

pred px_accepts[m: set Proposer -> Receiver, px: Proposer, rx: Receiver] {
    some px.px_pref[rx]
    let mx = m[px] | some mx => px.px_pref[rx] < px.px_pref[mx]
}

pred rx_accepts[m: set Proposer -> Receiver, px: Proposer, rx: Receiver] {
    some rx.rx_pref[px]
    let mx = m.rx | some mx => rx.rx_pref[px] < rx.rx_pref[mx]
}

pred stable_blocking_pair[m: set Proposer -> Receiver] {
    no px: Proposer, rx: Receiver | {
        px_accepts[m, px, rx]
        rx_accepts[m, px, rx]
    }
}

// individual rationality: A matching is individually rational if each participant
// prefers their assigned match to being unmatched
pred stable_rationality[m: set Proposer -> Receiver] {
    // if a participant is matched, they must have a preference for the other person
    all px: Proposer | m[px] in px.px_pref.Int
    all rx: Receiver | m.rx in rx.rx_pref.Int
}

pred stable[m: set Proposer -> Receiver] {
    stable_blocking_pair[m]
    stable_rationality[m]
}

--------------- stable matching algorithm -------------------------------------

fun none_min[ints: set Int]: lone Int {
    some ints => min[ints] else none
}

one sig Status {
    var offer: set Proposer -> Receiver
}

pred initial_status {
    Status.offer = px_pref.0
}

pred matching_step {
    -- if a proposer couldn't make any offers, they can't make one now
    Status.offer'.Receiver in Status.offer.Receiver

    -- each receiver chooses their favorite offering proposer, and rejects all others 
    all rx: Receiver {
        let best_px = rx.rx_pref.(none_min[rx.rx_pref[Status.offer.rx]]) {
            Status.offer'[best_px] = (some best_px => rx else none)
            all rejected_px: Status.offer.rx - best_px {
                Status.offer'[rejected_px]
                    = rejected_px.px_pref.(add[1, rejected_px.px_pref[rx]])
            }
        }
    }
}

pred terminal_status {
    -- receivers end up with at most one offer: an offer that they are okay with
    all rx: Receiver | lone Status.offer.rx and Status.offer.rx in rx.rx_pref.Int
}

run {
    initial_status

    always well_formed_preferences
    always matching_step
    eventually terminal_status

    all rx: Receiver | #rx.rx_pref = 3
    all px: Proposer | #px.px_pref = 3

    // all px : Proposer | Receiver in (px.px_pref).Int
    // #Proposer.(Status.offer) = 2
    // #Proposer.px_pref.0 >1
} for exactly 3 Receiver, exactly 3 Proposer

--------------- end stable matching algorithm -------------------------------------

//A set of employers with unfilled positions
//A one-dimensional array indexed by employers, specifying the preference index of the next applicant to whom the employer would send an offer, initially 1 for each employer
//A two-dimensional array indexed by an employer and a number i {\displaystyle i} from 1 to n {\displaystyle n}, naming the applicant who is each employer's i {\displaystyle i}th preference
//A one-dimensional array indexed by applicants, specifying their current employer, initially a sentinel value such as 0 indicating they are unemployed
//A two-dimensional array indexed by an applicant and an employer, specifying the position of that employer in the applicant's preference list

// https://csci1710.github.io/forge-documentation/forge-standard-library/helpers.html?highlight=sequen#sequence-helpers

//Gale–Shapley algorithm

/**

STEP 1: Step 1
--Each proposer proposes to his most preferred, acceptable receiver.
(if a proposer finds all receiver unacceptable they match to themselves).

--Each receiver who received at least one offer
temporarily holds the offer from the most preferred proposer among those
who made an offer to her and are acceptable rejects the other offer(s).


Step k, k ≥ 2

--Each proposer whose offer has been rejected in the previous step proposes to
his most preferred receiver among the acceptable receivers they has not yet
proposed to.
(if there is no such receiver they match to themselves).


--Each receiver who received at least one offer in this step
temporarily holds the offer from the most preferred proposer among
    1)those who made an offer to her in this step and are acceptable.
    2)the proposer she held from the previous step (if any).
rejects the other offer(s)


End: The algorithm stops when no proposer has an offer that is rejected.


Final matching:
Each receiver is matched to the proposer whose offer she was holding
when the algorithm stopped (if any).

Each proposer is matched to the receiver they were temporarily matched
when the algorithm stoped (if any).

*/
