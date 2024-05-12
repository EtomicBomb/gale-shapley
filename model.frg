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

// absence of blocking pair: no pair of proposers and receivers would rather
// be with eachother than their current match
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

sig PxPrefs {
    m_px_prefs: func Proposer -> PxPref
}

sig RxPrefs {
    m_rx_prefs: func Receiver -> RxPref
}

fun none_min[ints: set Int]: lone Int {
    some ints => min[ints] else none
}

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
