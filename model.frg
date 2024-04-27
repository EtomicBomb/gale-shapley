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
    Receiver.(px.px_pref) = { i: Int | 0 <= i and i < #{px.px_pref} }
}

// ordered preferences, with the numbers 1 to n
pred wellformed_rx_pref[rx: Receiver] {
    Proposer.(rx.rx_pref) = { i: Int | 0 <= i and i < #{rx.rx_pref} }
}

sig Matching {
    matching: pfunc Proposer -> Receiver
}

// matching is bijective, but may exclude some Proposers or Receivers
pred wellformed_matching[m: Matching] {
    all rx: Receiver | lone (m.matching).rx
}

// absence of a blocking pair: A matching is stable if there is no pair of participants who prefer each other to their assigned match
pred stable_blocking_pair[m: Matching] {
    no px: Proposer, rx: Receiver | {
        px_accepts[m, px, rx]
        rx_accepts[m, px, rx]
    }
}

pred px_accepts[m: Matching, px: Proposer, rx: Receiver] {
    let mx = px.(m.matching) | 
        some mx => rx.(px.px_pref) < mx.(px.px_pref) else some rx.(px.px_pref)
}

pred rx_accepts[m: Matching, px: Proposer, rx: Receiver] {
    let mx = (m.matching).rx |
        some mx => px.(rx.rx_pref) < mx.(rx.rx_pref) else some px.(rx.rx_pref)
}

pred wellformed_matching_px_pref_rx_pref {
    all m: Matching | wellformed_matching[m]
    all px: Proposer | wellformed_px_pref[px]
    all rx: Receiver | wellformed_rx_pref[rx]
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

pred wellformed_matching_px_pref_rx_pref {
    all m: Matching | wellformed_matching[m]
    all px: Proposer | wellformed_px_pref[px]
    all rx: Receiver | wellformed_rx_pref[rx]
}


--------------- stable matching algorithm -------------------------------------


sig State {
    offer: pfunc Proposer -> Receiver,
    partial_matching: one Matching,
    next: lone State
}

pred initial_state[s: State] {
    all px: Proposer | px.(s.offer) = (px.px_pref).0    
    no s.partial_matching.matching
}

pred terminal_state[s: State] {
    no s.offer
}

// advance. If px runs out of preferences, we leave px with no next rx
pred advance_offer[s: State, px: Proposer, rx: Receiver] {
    let next_rx = (px.px_pref).(rx.(px.px_pref) + 1) |
        s.next.offer = s.offer - (px -> Receiver) - (Proposer -> rx) + (px -> next_rx)
}

// px was able to make a proposal that was either accepted or rejected
pred offer_success[s: State, px: Proposer] {
    some rx: px.(s.offer) {
        s.next.partial_matching.matching = (rx_accepts[s.partial_matching, px, rx] => {
            s.partial_matching.matching - (px -> Receiver) - (Proposer -> rx) + (px -> rx)
        } else {
            s.partial_matching.matching
        })
        advance_offer[s, px, rx]
    }
}

// px has no offers left, so we have a dummy round
pred offer_failed[s: State, px: Proposer] {
    no px.(s.offer)
    s.next.offer = s.offer
    s.next.partial_matching = s.partial_matching
}

sig Round {
    next_round: lone Round,
    states: func Proposer -> State
}

// the round is a contiguous block of States
// offers happen between all the States
pred wellformed_round[round: Round] {
    let ss = Proposer.(round.states) | ss = ss.*next & ss.*(~next)
    all px: (round.states).State | let s = px.(round.states) {
        offer_success[s, px] or offer_failed[s, px]
    }
}

pred wellformed_rounds[first: Round] {
    all round: first + first.^next_round {
        wellformed_round[round]
        some last_state: Proposer.(round.states) | last_state.next in Proposer.(round.next_round.states)
    }
    no first.(~next_round)
    some first_state: Proposer.(first.states) | initial_state[first_state]
    some last_round: first.*next_round {
        no last_round.next_round
        some s: Proposer.(last_round.states) | terminal_state[s]
    }
}

run {
    all m: Matching | wellformed_matching[m]
    all px: Proposer | wellformed_px_pref[px]
    all rx: Receiver | wellformed_rx_pref[rx]
    some first: Round | wellformed_rounds[first]
} for {next is linear}
// TODO: need another is linear bound for next_round

--------------- end stable matching algorithm -------------------------------------

/*
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

//A set of employers with unfilled positions
//A one-dimensional array indexed by employers, specifying the preference index of the next applicant to whom the employer would send an offer, initially 1 for each employer
//A two-dimensional array indexed by an employer and a number i {\displaystyle i} from 1 to n {\displaystyle n}, naming the applicant who is each employer's i {\displaystyle i}th preference
//A one-dimensional array indexed by applicants, specifying their current employer, initially a sentinel value such as 0 indicating they are unemployed
//A two-dimensional array indexed by an applicant and an employer, specifying the position of that employer in the applicant's preference list

// https://csci1710.github.io/forge-documentation/forge-standard-library/helpers.html?highlight=sequen#sequence-helpers

//Gale–Shapley algorithm

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
