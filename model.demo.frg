#lang forge/temporal
open "model.frg"

run {
    some s: Status, px_prefs: PxPrefs, rx_prefs: RxPrefs {
        //just to ensure that all proposers and receivers have 3 preferences
        #(px_prefs.m_px_prefs) >= 3
        #(rx_prefs.m_rx_prefs) >= 3
        initial_status[s, px_prefs.m_px_prefs, rx_prefs.m_rx_prefs]
        always well_formed_preferences
        always matching_step[s, px_prefs.m_px_prefs, rx_prefs.m_rx_prefs]
        not next_state terminal_status[s, px_prefs.m_px_prefs, rx_prefs.m_rx_prefs]
        not next_state next_state terminal_status[s, px_prefs.m_px_prefs, rx_prefs.m_rx_prefs]
    }
} for exactly 0 Matching, 3 Receiver, exactly 3 Proposer, exactly 1 RxPrefs, exactly 1 PxPrefs, exactly 1 Status

pred twoPxCollusion[px1, px2: Proposer, true_px_prefs, false_px_prefs: PxPrefs] {
    all px: Proposer - px1 - px2 {
        false_px_prefs.m_px_prefs.m_px_pref[px] = true_px_prefs.m_px_prefs.m_px_pref[px] 
    }
}

-- two pxs collude
run {
    some disj s1, s2: Status, rx_prefs: RxPrefs, true_px_prefs, false_px_prefs: PxPrefs, px1, px2: Proposer {
        `PxPrefs0 = false_px_prefs
        `Status0 = s2
        `Proposer0 = px1
        `Proposer1 = px2
        `PxPrefs1 = true_px_prefs
        `Status1 = s1
        twoPxCollusion[px1, px2, true_px_prefs, false_px_prefs]
        #(true_px_prefs.m_px_prefs) >= 3
        all px: Proposer | #((true_px_prefs.m_px_prefs[px]).m_px_pref) >= 3
        initial_status[s1, true_px_prefs.m_px_prefs, rx_prefs.m_rx_prefs]
        initial_status[s2, false_px_prefs.m_px_prefs, rx_prefs.m_rx_prefs]
        always well_formed_preferences
        always matching_step[s1, true_px_prefs.m_px_prefs, rx_prefs.m_rx_prefs]
        always matching_step[s2, false_px_prefs.m_px_prefs, rx_prefs.m_rx_prefs]
        eventually {
            terminal_status[s1, true_px_prefs.m_px_prefs, rx_prefs.m_rx_prefs]
            terminal_status[s2, false_px_prefs.m_px_prefs, rx_prefs.m_rx_prefs]
            let px1_pref = true_px_prefs.m_px_prefs.m_px_pref[px1] {
                let px2_pref = true_px_prefs.m_px_prefs.m_px_pref[px2] {
                    some px1_pref[s1.offer[px1]]
                    some px1_pref[s2.offer[px1]]
                    px1_pref[s2.offer[px1]] < px1_pref[s1.offer[px1]]
                }
            }
        }
    }
} for 0 Matching, 3 Receiver, 3 Proposer, exactly 1 RxPrefs, exactly 2 PxPrefs, exactly 2 Status

pred pxLies[lying_px: Proposer, true_px_prefs, false_px_prefs: PxPrefs] {
    //all receiver except lying_px have the same preferences
    all px : Proposer - lying_px {
        false_px_prefs.m_px_prefs.m_px_pref[px] = true_px_prefs.m_px_prefs.m_px_pref[px] 
    }
    //lying only represents their most preferred proposer and no one else
    false_px_prefs.m_px_prefs.m_px_pref[lying_px] != true_px_prefs.m_px_prefs.m_px_pref[lying_px] 
}

pred rxLies[lying_rx: Receiver, true_rx_prefs, false_rx_prefs: RxPrefs] {
    //all receiver except lying_rx have the same preferences
    all rx : Receiver - lying_rx {
        false_rx_prefs.m_rx_prefs.m_rx_pref[rx] = true_rx_prefs.m_rx_prefs.m_rx_pref[rx] 
    }
    //lying only represents their most preferred proposer and no one else
    false_rx_prefs.m_rx_prefs.m_rx_pref[lying_rx] != true_rx_prefs.m_rx_prefs.m_rx_pref[lying_rx] 
}

-- the rx lies and benefits
run {
    some disj s1, s2: Status, px_prefs: PxPrefs, true_rx_prefs, false_rx_prefs: RxPrefs, lying_rx: Receiver {
        `RxPrefs0 = false_rx_prefs
        `Status0 = s2
        `Receiver0 = lying_rx
        `RxPrefs1 = true_rx_prefs
        `Status1 = s1
        #(true_rx_prefs.m_rx_prefs) >= 3
        rxLies[lying_rx, true_rx_prefs, false_rx_prefs]

        initial_status[s1, px_prefs.m_px_prefs, true_rx_prefs.m_rx_prefs]
        initial_status[s2, px_prefs.m_px_prefs, false_rx_prefs.m_rx_prefs]
        always well_formed_preferences
        always matching_step[s1, px_prefs.m_px_prefs, true_rx_prefs.m_rx_prefs]
        always matching_step[s2, px_prefs.m_px_prefs, false_rx_prefs.m_rx_prefs]
        eventually {
            terminal_status[s1, px_prefs.m_px_prefs, true_rx_prefs.m_rx_prefs]
            terminal_status[s2, px_prefs.m_px_prefs, false_rx_prefs.m_rx_prefs]
            let lying_pref = true_rx_prefs.m_rx_prefs.m_rx_pref[lying_rx] {
                some lying_pref[s2.offer.lying_rx]
                some lying_pref[s1.offer.lying_rx]
                lying_pref[s2.offer.lying_rx] < lying_pref[s1.offer.lying_rx]
            }
            //lying_rx gets a more favorable match under s2 than s1, according to their true_rx_prefs
        }
    }
} for exactly 0 Matching, 3 Receiver, exactly 3 Proposer, exactly 1 PxPrefs, exactly 2 RxPrefs, exactly 2 Status

-- px rx collusion
run {
    some disj s1, s2: Status, true_px_prefs, false_px_prefs: PxPrefs, true_rx_prefs, false_rx_prefs: RxPrefs, lying_px: Proposer, lying_rx: Receiver {
        `PxPrefs0 = false_px_prefs
        `RxPrefs0 = false_rx_prefs
        `Receiver0 = lying_rx
        `Proposer0 = lying_px
        `Status0 = s2
        `PxPrefs1 = true_px_prefs
        `RxPrefs1 = true_rx_prefs
        `Status1 = s1
        #(true_px_prefs.m_px_prefs) >= 3
        #(true_rx_prefs.m_rx_prefs) >= 3
        pxLies[lying_px, true_px_prefs, false_px_prefs]
        rxLies[lying_rx, true_rx_prefs, false_rx_prefs]
        initial_status[s1, true_px_prefs.m_px_prefs, true_rx_prefs.m_rx_prefs]
        initial_status[s2, false_px_prefs.m_px_prefs, false_rx_prefs.m_rx_prefs]
        always well_formed_preferences
        always matching_step[s1, true_px_prefs.m_px_prefs, true_rx_prefs.m_rx_prefs]
        always matching_step[s2, false_px_prefs.m_px_prefs, false_rx_prefs.m_rx_prefs]
        eventually {
            terminal_status[s1, true_px_prefs.m_px_prefs, true_rx_prefs.m_rx_prefs]
            terminal_status[s2, false_px_prefs.m_px_prefs, false_rx_prefs.m_rx_prefs]
            //lying_px gets a more favorable match under s2 than s1, according to their true_px_prefs
            let lying_pref = true_px_prefs.m_px_prefs.m_px_pref[lying_px] {
                some lying_pref[s1.offer[lying_px]]
                some lying_pref[s2.offer[lying_px]]
                lying_pref[s2.offer[lying_px]] < lying_pref[s1.offer[lying_px]]
            }        
        }
    }
} for exactly 0 Matching, 3 Receiver, exactly 3 Proposer, exactly 2 RxPrefs, exactly 2 PxPrefs, exactly 2 Status

-- px rx collusion, rx benefits
run {
    some disj s1, s2: Status, true_px_prefs, false_px_prefs: PxPrefs, true_rx_prefs, false_rx_prefs: RxPrefs, lying_px: Proposer, lying_rx: Receiver {
        `PxPrefs0 = false_px_prefs
        `RxPrefs0 = false_rx_prefs
        `Receiver0 = lying_rx
        `Proposer0 = lying_px
        `Status0 = s2
        `PxPrefs1 = true_px_prefs
        `RxPrefs1 = true_rx_prefs
        `Status1 = s1
        pxLies[lying_px, true_px_prefs, false_px_prefs]
        rxLies[lying_rx, true_rx_prefs, false_rx_prefs]
        //just to ensure that all proposers and receivers have 3 preferences
        #(true_px_prefs.m_px_prefs) >= 3
        #(true_rx_prefs.m_rx_prefs) >= 3

        initial_status[s1, true_px_prefs.m_px_prefs, true_rx_prefs.m_rx_prefs]
        initial_status[s2, false_px_prefs.m_px_prefs, false_rx_prefs.m_rx_prefs]
        always well_formed_preferences
        always matching_step[s1, true_px_prefs.m_px_prefs, true_rx_prefs.m_rx_prefs]
        always matching_step[s2, false_px_prefs.m_px_prefs, false_rx_prefs.m_rx_prefs]
        eventually {
            terminal_status[s1, true_px_prefs.m_px_prefs, true_rx_prefs.m_rx_prefs]
            terminal_status[s2, false_px_prefs.m_px_prefs, false_rx_prefs.m_rx_prefs]
            
            //lying_rx gets a more favorable match under s2 than s1, according to their true_rx_prefs
            let lying_pref = true_rx_prefs.m_rx_prefs.m_rx_pref[lying_rx] {
                some lying_pref[s2.offer.lying_rx]
                some lying_pref[s1.offer.lying_rx]
                lying_pref[s2.offer.lying_rx] < lying_pref[s1.offer.lying_rx]
            }
        }
    }
} for exactly 0 Matching, 3 Receiver, exactly 3 Proposer, exactly 2 RxPrefs, exactly 2 PxPrefs, exactly 2 Status