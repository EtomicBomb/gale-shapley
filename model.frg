#lang forge/temporal
option max_tracelength 10
option run_sterling "model_vis.js"

sig RxPref {
    m_rx_pref: pfunc Proposer -> Int // Receivers rank Proposers
}

sig PxPref {
    m_px_pref: pfunc Receiver -> Int // Proposers rank Receivers
}

sig Receiver {}

sig Proposer {}

-- TODO: create new sigs ReceiverPreferences and ProposerPreferences,
-- which are paramaters for stable*[] predicates
-- then, we can alter these to see the impact on the resulting matches?
-- note: pfunc constraint cannot be expressed: illegal syntax: Receiver -> pfunc Proposer -> Int

// ordered preferences, with the numbers 1 to n
pred wellformed_px_pref[px_pref: PxPref] {
    px_pref.m_px_pref[Receiver] = { i: Int | 0 <= i and i < #{px_pref.m_px_pref} }
}

// ordered preferences, with the numbers 1 to n
pred wellformed_rx_pref[rx_pref: RxPref] {
    rx_pref.m_rx_pref[Proposer] = { i: Int | 0 <= i and i < #{rx_pref.m_rx_pref} }
}

pred well_formed_preferences {
    all px_pref: PxPref | wellformed_px_pref[px_pref]
    all rx_pref: RxPref | wellformed_rx_pref[rx_pref]
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
    well_formed_preferences
}

pred stable_blocking_pair[m: set Proposer -> Receiver, px_prefs: func Proposer -> PxPref, rx_prefs: func Receiver -> RxPref] {
    no px: Proposer, rx: Receiver | {
        some px_prefs[px].m_px_pref[rx]
        some rx_prefs[rx].m_rx_pref[px]
        let mx = m[px] | some mx => px_prefs[px].m_px_pref[rx] < px_prefs[px].m_px_pref[mx]
        let mx = m.rx | some mx => rx_prefs[rx].m_rx_pref[px] < rx_prefs[rx].m_rx_pref[mx]
    }
}

// individual rationality: A matching is individually rational if each participant
// prefers their assigned match to being unmatched
pred stable_rationality[m: set Proposer -> Receiver, px_prefs: func Proposer -> PxPref, rx_prefs: func Receiver -> RxPref] {
    // if a participant is matched, they must have a preference for the other person
    all px: Proposer | m[px] in px_prefs[px].m_px_pref.Int
    all rx: Receiver | m.rx in rx_prefs[rx].m_rx_pref.Int
}

pred stable[m: set Proposer -> Receiver, px_prefs: func Proposer -> PxPref, rx_prefs: func Receiver -> RxPref] {
    stable_blocking_pair[m, px_prefs, rx_prefs]
    stable_rationality[m, px_prefs, rx_prefs]
}

--------------- stable matching algorithm -------------------------------------

fun none_min[ints: set Int]: lone Int {
    some ints => min[ints] else none
}

--px_prefs.m_px_prefs -- func Proposer -> PxPref
--px_prefs.m_px_prefs.m_px_pref -- func Proposer -> Receiver -> Int
--px_prefs.m_px_prefs.m_px_pref.0 -- func Proposer -> Receiver

-- px.px_prefs -> px_prefs.m_px_prefs.m_px_pref[px] -- Receiver -> Int
-- rx.rx_prefs -> rx_prefs.m_rx_prefs.m_rx_pref[rx] -- Proposer -> Int



 sig Status {
    var offer: set Proposer -> Receiver
}

pred initial_status[s: Status, px_prefs: func Proposer -> PxPref, rx_prefs: func Receiver -> RxPref] {
    s.offer = px_prefs.m_px_pref.0
}

pred matching_step[s: Status, px_prefs: func Proposer -> PxPref, rx_prefs: func Receiver -> RxPref] {
    -- if a proposer couldn't make any offers, they can't make one now
    s.offer'.Receiver in s.offer.Receiver

    -- each receiver chooses their favorite offering proposer, and rejects all others 
    all rx: Receiver {
        let best_px = (rx_prefs.m_rx_pref[rx]).(none_min[rx_prefs.m_rx_pref[rx][s.offer.rx]]) {
            s.offer'[best_px] = (some best_px => rx else none)
            all rejected_px: s.offer.rx - best_px {
                s.offer'[rejected_px]
                    = (px_prefs.m_px_pref[rejected_px]).(add[1, px_prefs.m_px_pref[rejected_px][rx]])
            }
        }
    }
}

pred terminal_status[s: Status, px_prefs: func Proposer -> PxPref, rx_prefs: func Receiver -> RxPref] {
    -- receivers end up with at most one offer: an offer that they are okay with
    all rx: Receiver | lone s.offer.rx and s.offer.rx in (rx_prefs.m_rx_pref[rx]).Int
}

sig PxPrefs {
    m_px_prefs: func Proposer -> PxPref
}

sig RxPrefs {
    m_rx_prefs: func Receiver -> RxPref
}


pred lying[lying_rx: Receiver, true_rx_prefs, false_rx_prefs: RxPrefs] {
    //all receiver except lying_rx have the same preferences
    all rx : Receiver - lying_rx {
        false_rx_prefs.m_rx_prefs.m_rx_pref[rx] = true_rx_prefs.m_rx_prefs.m_rx_pref[rx] 
    }
    //lying only represents their most preferred proposer and no one else
    false_rx_prefs.m_rx_prefs.m_rx_pref[lying_rx] != true_rx_prefs.m_rx_prefs.m_rx_pref[lying_rx] 
}

// run {
//     some disj s1, s2: Status, px_prefs: PxPrefs, true_rx_prefs, false_rx_prefs: RxPrefs, lying_rx: Receiver {
//         lying[lying_rx, true_rx_prefs, false_rx_prefs]
//         //just to ensure that all proposers and receivers have 3 preferences
//         all px: Proposer | #((px_prefs.m_px_prefs[px]).m_px_pref) = 3
//         all rx: Receiver | #((true_rx_prefs.m_rx_prefs[rx]).m_rx_pref) = 3

//         initial_status[s1, px_prefs.m_px_prefs, true_rx_prefs.m_rx_prefs]
//         initial_status[s2, px_prefs.m_px_prefs, false_rx_prefs.m_rx_prefs]
//         always well_formed_preferences
//         always matching_step[s1, px_prefs.m_px_prefs, true_rx_prefs.m_rx_prefs]
//         always matching_step[s2, px_prefs.m_px_prefs, false_rx_prefs.m_rx_prefs]
//         eventually {
//             terminal_status[s1, px_prefs.m_px_prefs, true_rx_prefs.m_rx_prefs]
//             terminal_status[s2, px_prefs.m_px_prefs, false_rx_prefs.m_rx_prefs]
//             //lying_rx gets a more favorable match under s2 than s1, according to their true_rx_prefs
//             true_rx_prefs.m_rx_prefs.m_rx_pref[lying_rx][s2.offer.lying_rx] < true_rx_prefs.m_rx_prefs.m_rx_pref[lying_rx][s1.offer.lying_rx]
           
//         }
//     }
// } for exactly 3 Receiver, exactly 3 Proposer, exactly 1 PxPrefs, exactly 2 RxPrefs, exactly 2 Status


run {
    some s: Status, px_prefs: PxPrefs, rx_prefs: RxPrefs {
        initial_status[s, px_prefs.m_px_prefs, rx_prefs.m_rx_prefs]
        always well_formed_preferences
        always matching_step[s, px_prefs.m_px_prefs, rx_prefs.m_rx_prefs]
        eventually terminal_status[s, px_prefs.m_px_prefs, rx_prefs.m_rx_prefs]
        all px: Proposer | #((px_prefs.m_px_prefs[px]).m_px_pref) = 3
        all rx: Receiver | #((rx_prefs.m_rx_prefs[rx]).m_rx_pref) = 3
        // #Proposer.(Status.offer) = 2
    }

   
} for exactly 3 Receiver, exactly 3 Proposer, exactly 1 RxPrefs, exactly 1 PxPrefs, exactly 1 Status

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
