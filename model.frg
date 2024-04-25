#lang forge/temporal

sig Receiver {
    rx_pref: pfunc Proposer -> Int
}

sig Proposer {
    px_pref: pfunc Receiver -> Int
}

// ordered preferences, with the numbers 1 to n
pred px_pref_wellformed[px: Proposer] {
    Receiver.(px.px_pref) = { i: Int | 0 <= i and i < #{px.px_pref} }
}

// ordered preferences, with the numbers 1 to n
pred rx_pref_wellformed[rx: Receiver] {
    Proposer.(rx.rx_pref) = { i: Int | 0 <= i and i < #{rx.rx_pref} }
}

test expect {
    manyRxPreferences: {
        some rx: Receiver | rx_pref_wellformed[rx] and #{rx.rx_pref} = 5
    } for exactly 1 Receiver, 5 Proposer is sat
    manyPxPreferences: {
        some px: Proposer | px_pref_wellformed[px] and #{px.px_pref} = 5
    } for exactly 1 Proposer, 5 Receiver is sat

    pxAlwaysZero: {
        all px: Proposer | px_pref_wellformed[px] and some px.px_pref => 0 in Receiver.(px.px_pref)
    } for 5 Receiver, 5 Proposer is theorem
    rxAlwaysZero: {
        all rx: Receiver | rx_pref_wellformed[rx] and some rx.rx_pref => 0 in Proposer.(rx.rx_pref)
    } for 5 Receiver, 5 Proposer is theorem

    rxPrefSeq: {
        all rx: Receiver | rx_pref_wellformed[rx] => isSeqOf[~(rx.rx_pref), Proposer]
    } for exactly 1 Receiver, 5 Proposer is theorem
    pxPrefSeq: {
        all px: Proposer | px_pref_wellformed[px] => isSeqOf[~(px.px_pref), Receiver]
    } for exactly 1 Proposer, 5 Receiver is theorem
}

sig Matching {
    matching: pfunc Proposer -> Receiver
}

// matching is bijective, but may exclude some Proposers or Receivers
pred matching_wellformed[m: Matching] {
    all rx: Receiver | lone (m.matching).rx
}

test expect {
    wellformedSometimes: {
        some m: Matching, px: Proposer, rx: Receiver | matching_wellformed[m] and (px -> rx) in m.matching
    } for 5 Proposer, 5 Receiver is sat
    bijectiveMatching: {
        // after we remove px -> rx from a match, there's nothing involving px or rx
        all m: Matching, px: Proposer, rx: Receiver | (px -> rx) in m.matching => {
            matching_wellformed[m] => {
                no (m.matching - px -> rx) & (px -> Receiver + Proposer -> rx)
            }
        }
    } for 5 Proposer, 5 Receiver is theorem
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
        some mx => rx.(px.px_pref) > mx.(px.px_pref) else some rx.(px.px_pref)
}

pred rx_accepts[m: Matching, px: Proposer, rx: Receiver] {
    let mx = (m.matching).rx |
        some mx => px.(rx.rx_pref) > mx.(rx.rx_pref) else some px.(rx.rx_pref)
}

pred wellformed_matching_px_pref_rx_pref {
    all m: Matching | matching_wellformed[m]
    all px: Proposer | px_pref_wellformed[px]
    all rx: Receiver | rx_pref_wellformed[rx]
}

test expect {
    unstableTwoNoAssignment: {
        all m: Matching {
            {
                wellformed_matching_px_pref_rx_pref
                some px: Proposer, rx: Receiver {
                    some rx.(px.px_pref)
                    some px.(rx.rx_pref)
                    no px.(m.matching)
                    no (m.matching).rx
                }
            } => not stable_blocking_pair[m]
        }
    } for 1 Matching, 5 Proposer, 5 Receiver is theorem
    // ^ this test, but if they both have matchings, or if only one has a matching

    // a test for a non-trivial scenario where we imply stable_blocking_pair (instead of not stable blocking pair)
}

// individual rationality: A matching is individually rational if each participant 
// prefers their assigned match to being unmatched
pred stable_rationality[m: Matching] {
    // if a participant is matched, they must have a preference for the other person
    all px: Proposer | px.(m.matching) in (px.px_pref).Int
    all rx: Receiver | (m.matching).rx in (rx.rx_pref).Int
}

test expect {
    allPreferencesSanity: {
        wellformed_matching_px_pref_rx_pref
        all px: Proposer, rx: Receiver {
            #{px.px_pref} > 3
            #{rx.rx_pref} > 3
            (px.px_pref).Int = Receiver
            (rx.rx_pref).Int = Proposer
        }
    } for 1 Matching, 5 Proposer, 5 Receiver is sat
    // if everyone has a preference for everyone, we're certainly stable_rationality
    allPreferences: {
        all m: Matching {
            {
                wellformed_matching_px_pref_rx_pref
                all px: Proposer, rx: Receiver {
                    (px.px_pref).Int = Receiver
                    (rx.rx_pref).Int = Proposer
                }
            } => stable_rationality[m]
        }
    } for 1 Matching, 5 Proposer, 5 Receiver is theorem
}

pred stable[m: Matching] {
    stable_blocking_pair[m]
    stable_rationality[m]
}

test expect {
    stableSat: {
        some m: Matching | some m.matching and stable[m]
    } for 5 Proposer, 5 Receiver is sat
    stableNotSat: {
        some m: Matching | some m.matching and not stable[m]
    } for 5 Proposer, 5 Receiver is sat

    stableNoPrefs: {
        all m: Matching {
            (all px: Proposer, rx: Receiver {
                wellformed_matching_px_pref_rx_pref
                no px.px_pref
                no rx.rx_pref
                no m.matching
            }) => stable[m]
        } 
    } for 5 Proposer, 5 Receiver is theorem

}


--------------- stable matching algorithm -------------------------------------



sig Status {
    offer: pfunc Proposer -> Receiver,
    partial_matching: one Matching,
    next_status: lone Status
}

pred initial_state[s: Status] {
    all px: Proposer | px.(s.offer) = (px.px_pref).0    
    no s.partial_matching.matching
}

pred terminal_state[s: Status] {
    no s.offer
}

// advance. If px runs out of preferences, we leave px with no next rx
pred advance_offer[s: Status, px: Proposer, rx: Receiver] {
    let next_rx = (px.px_pref).(rx.(px.px_pref) + 1) |
        s.next_status.offer = s.offer - (px -> Receiver) - (Proposer -> rx) + (px -> next_rx)
}

// px was able to make a proposal that was either accepted or rejected
pred offer_success[s: Status, px: Proposer] {
    some rx: px.(s.offer) {
        s.next_status.partial_matching.matching = (rx_accepts[s.partial_matching, px, rx] => {
            s.partial_matching.matching - (px -> Receiver) - (Proposer -> rx) + (px -> rx)
        } else {
            s.partial_matching.matching
        })
        advance_offer[s, px, rx]
    }
}

// px has no offers left, so we have a dummy round
pred offer_failed[s: Status, px: Proposer] {
    no px.(s.offer)
    s.next_status.offer = s.offer
    s.next_status.partial_matching = s.partial_matching
}

sig Round {
    next_round: lone Round,
    states: func Proposer -> Status
}

// the round is a contiguous block of States
// offers happen between all the States
pred round_wellformed[round: Round] {
    let ss = Proposer.(round.states) | some first, last: ss {
        // first and last step are actually the first and last in ss
        ss in first.*next_status + last.*(~next_status)
        // nothing else is between the first and last steps
        ss = first.*next_status & last.*(~next_status)
    }
    all px: (round.states).Status | let s = px.(round.states) {
        offer_success[s, px] or offer_failed[s, px]
    }
}

pred rounds_wellformed[first: Round] {
    all round: first + first.^next_round {
        round_wellformed[round]
        some last_state: Proposer.(round.states) | last_state.next_status in Proposer.(round.next_round.states)
    }
    no first.(~next_round)
    some first_state: Proposer.(first.states) | initial_state[first_state]
    some last_round: first.*next_round {
        no last_round.next_round
        some s: Proposer.(last_round.states) | terminal_state[s]
    }
}

run {
    all m: Matching | matching_wellformed[m]
    all px: Proposer | px_pref_wellformed[px]
    all rx: Receiver | rx_pref_wellformed[rx]
    some first: Round | rounds_wellformed[first]
} for {next_status is linear}
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
    stable
    --action
    --no matching
}

pred traces{
    wellformed

    init_state
    eventually final_state
}

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
