#lang forge

sig Receiver {
    rx_pref: pfunc Proposer -> Int
}

sig Proposer {
    px_pref: pfunc Receiver -> Int
}

// ordered preferences, with the numbers 1 to n
pred wellformed_px_pref[px: Proposer] {
    Receiver.(px.px_pref) = { i: Int | 0 <= i and i < #{px.px_pref} }
}

// ordered preferences, with the numbers 1 to n
pred wellformed_rx_pref[rx: Receiver] {
    Proposer.(rx.rx_pref) = { i: Int | 0 <= i and i < #{rx.rx_pref} }
}

test expect {
    manyRxPreferences: {
        some rx: Receiver | wellformed_rx_pref[rx] and #{rx.rx_pref} = 5
    } for exactly 1 Receiver, 5 Proposer is sat
    manyPxPreferences: {
        some px: Proposer | wellformed_px_pref[px] and #{px.px_pref} = 5
    } for exactly 1 Proposer, 5 Receiver is sat

    pxAlwaysZero: {
        all px: Proposer | wellformed_px_pref[px] and some px.px_pref => 0 in Receiver.(px.px_pref)
    } for 5 Receiver, 5 Proposer is theorem
    rxAlwaysZero: {
        all rx: Receiver | wellformed_rx_pref[rx] and some rx.rx_pref => 0 in Proposer.(rx.rx_pref)
    } for 5 Receiver, 5 Proposer is theorem

    rxPrefSeq: {
        all rx: Receiver | wellformed_rx_pref[rx] => isSeqOf[~(rx.rx_pref), Proposer]
    } for exactly 1 Receiver, 5 Proposer is theorem
    pxPrefSeq: {
        all px: Proposer | wellformed_px_pref[px] => isSeqOf[~(px.px_pref), Receiver]
    } for exactly 1 Proposer, 5 Receiver is theorem
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
    all px: Proposer, rx: Receiver | wellformed_px_pref[px] and wellformed_rx_pref[rx]
}

test expect {
    wellformedSometimes: {
        some m: Matching, px: Proposer, rx: Receiver | wellformed_matching[m] and (px -> rx) in m.matching
    } for 5 Proposer, 5 Receiver is sat
    bijectiveMatching: {
        // after we remove px -> rx from a match, there's nothing involving px or rx
        all m: Matching, px: Proposer, rx: Receiver | (px -> rx) in m.matching => {
            wellformed_matching[m] => {
                no (m.matching - px -> rx) & (px -> Receiver + Proposer -> rx)
            }
        }
    } for 5 Proposer, 5 Receiver is theorem
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

test expect {
    stableBlockingPairSat: {
        some m: Matching | some m.matching and stable_blocking_pair[m]
    } for 5 Proposer, 5 Receiver is sat
    stableBlockingPairNotSat: {
        some m: Matching | some m.matching and not stable_blocking_pair[m]
    } for 5 Proposer, 5 Receiver is sat

    unstableTwoNoAssignment: {
        all m: Matching | {
            {
                wellformed
                some px: Proposer, rx: Receiver {
                    some rx.(px.px_pref)
                    some px.(rx.rx_pref)
                    no px.(m.matching)
                    no (m.matching).rx
                }
            } => not stable_blocking_pair[m]
        } 
    } for 1 Matching, 5 Proposer, 5 Receiver is theorem

}

// individual rationality: A matching is individually rational if each participant prefers their assigned match to being unmatched
pred stable_rationality[m: Matching] {
    // if a participant is matched, they must have a preference for the other person
    all px: Proposer | px.(m.matching) in (px.px_pref).Int    
    all rx: Receiver | (m.matching).rx in (rx.rx_pref).Int
}

test expect {
    stableRationalitySat: {
        some m: Matching | some m.matching and stable_rationality[m]
    } for 5 Proposer, 5 Receiver is sat
    stableRationalityNotSat: {
        some m: Matching | some m.matching and not stable_rationality[m]
    } for 5 Proposer, 5 Receiver is sat
}

pred stable[m: Matching] {
    stable_blocking_pair[m]
    stable_rationality[m]
}
