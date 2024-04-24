#lang forge/temporal
option max_tracelength 12

sig Receiver {
    rx_pref: pfunc Proposer -> Int // Receivers rank Proposers
}

sig Proposer {
    px_pref: pfunc Receiver -> Int // Proposers rank Receivers
}

// ordered preferences, with the numbers 1 to n
pred wellformed_px_pref[px: Proposer] {
    Receiver.(px.px_pref) = { i: Int | 0 <= i and i < #{Receiver} }
}

// ordered preferences, with the numbers 1 to n
pred wellformed_rx_pref[rx: Receiver] {
    Proposer.(rx.rx_pref) = { i: Int | 0 <= i and i < #{Proposer} }
}

sig Matching {
    matching: pfunc Proposer -> Receiver
}

// matching is bijective, but may exclude some Proposers or Receivers
pred wellformed_matching[m: Matching] {
    all rx: Receiver | lone rx.~(m.matching)
}

pred wellformed {
    all m: Matching | wellformed_matching[m]
    all px: Proposer | wellformed_px_pref[px]
    all rx: Receiver | wellformed_rx_pref[rx]
}

// absence of a blocking pair: A matching is stable if there is no pair of participants who prefer each other to their assigned match
pred stable_blocking_pair[m: Matching] {
    no px: Proposer, rx: Receiver | {
        let mx = px.(m.matching) |
            some mx => rx.(px.px_pref) > mx.(px.px_pref) else some rx.(px.px_pref)
        let mx = (m.matching).rx |
            some mx => px.(rx.rx_pref) > mx.(rx.rx_pref) else some px.(rx.rx_pref)
    }
}

// individual rationality: A matching is individually rational if each participant 
// prefers their assigned match to being unmatched
pred stable_rationality[m: Matching] {
    // if a participant is matched, they must have a preference for the other person
    all px: Proposer | px.(m.matching) in (px.px_pref).Int
    all rx: Receiver | (m.matching).rx in (rx.rx_pref).Int
}

pred stable[m: Matching] {
    stable_blocking_pair[m]
    stable_rationality[m]
}



pred init_state{
    --Guard:
    -- No matching
    no m: Matching | some m.matching



}

pred matching_step {
    --guard
    -- first state, they all propose to their most prefered person
    -- keep track of the matches
    --keep track
    --action
    --

    //seqFirst[proposer.pref] -- this is the most prefered receiver

}




pred update_State{

}


pred final_state{
    --guard
    //all proposers are matched?
    all m: Matching | stable[m]
    --action
    --no matching

}








pred traces{
   always wellformed
    init_state
    eventually final_state
}

run { 
    traces
} for exactly 2 Receiver, exactly 2 Proposer


//A proposer is matched with a receiver or themselves(and not another proposer)
//A receiver is matched with a proposer or themselves(and not another receiver)

// pred cant_match_same_type{
//     all p :proposer| all e: elems[p.pref] | (e in receiver +p)

//     all r: receiver| all e: elems[r.pref] | (e in proposer +r)

// }









/*
    A set of employers with unfilled positions
    A one-dimensional array indexed by employers, specifying the preference index of the next applicant to whom the employer would send an offer, initially 1 for each employer
    A two-dimensional array indexed by an employer and a number i {\displaystyle i} from 1 to n {\displaystyle n}, naming the applicant who is each employer's i {\displaystyle i}th preference
    A one-dimensional array indexed by applicants, specifying their current employer, initially a sentinel value such as 0 indicating they are unemployed
    A two-dimensional array indexed by an applicant and an employer, specifying the position of that employer in the applicant's preference list
    */





// https://csci1710.github.io/forge-documentation/forge-standard-library/helpers.html?highlight=sequen#sequence-helpers




//Gale–Shapley algorithm

/*
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