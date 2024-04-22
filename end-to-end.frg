#lang forge

abstract sig ProposePreference {
   
}

sig Receiver {
    rx_pref: pfunc Proposer -> Int
}

sig Proposer {
    pr_pref: pfunc Receiver -> Int
}


// ordered preferences, with the numbers 1 to n
pred wellformed_rx_pref[rx: Receiver] {
    Proposer.(rx.rx_pref) = { i: Int | 1 <= i and i <= #{rx.rx_pref} }
}

// ordered preferences, with the numbers 1 to n
pred wellformed_pr_pref[pr: Proposer] {
    Receiver.(pr.pr_pref) = { i: Int | 1 <= i and i <= #{pr.pr_pref} }
}

sig Matching {
    matching: pfunc Proposer -> Receiver
}

// matching is bijective
pred wellformed_matching[m: Matching] {
    // #{(m.matching).Receiver} = #{Proposer.(m.matching)}
    all rx: Receiver | lone (~m.matching)[rx]
}





//STABILITY:

//individual rationality: A matching is individually rational if each participant prefers their assigned match to being unmatched

pred stable[m: Matching] {

    let MatchedProposer = (m.matching).Recevier | let MatchedReceiver = Proposer.(m.matching) | {

    --both receiver and proposal have no match, but they have rank for eachother
    no pr: Proposer, rx: Receiver | {

        some (m.matching).pr 
            => pr.pr_pref[rx] > pr.pr_pref[m.matching[pr]] 
            else some pr.pr_pref[rx] 
        some rx.(m.matching)
            => 
        
        some rx.rx_pref[pr]
    }

    --both receiver and proposal have a match, but they like eachother more than their assignment
    no pr: MatchedProposer, rx: MatchedReceiver | {
        m.matching[pr] 
        some 
        some rx.rx_pref[pr] > rx.rx_pref[(~m.matching)[rx]]
    }

    --receiver has match, proposer no match
    no pr: Proposer - MatchedProposer, rx: MatchedReceiver | {
        some pr.pr_pref[rx]
        some pr.pr_pref[rx] > pr.pr_pref[m.matching[pr]]


        some rx.rx_pref[pr] > rx.rx_pref[(~m.matching)[rx]]
    }






    // individual rationality: every matched pr has a preference for their matched rx
    // individual rationality: every matched rx has a preference for their matched pr

    // abs
    //absence of a blocking pair: A matching is stable if there is no pair of participants who prefer each other to their assigned match



    no pr: MatchedProposer, rx: MatchedReceiver | {
        
    }


    all matched_pr:  | {
        in (Int -> (matched_pr.pr_pref)) in m.matching[matched_pr] 
    }
    all matched_rx: Proposer.(m.matching) | {
        m.matching[matched_pr] in (Int -> (matched_pr.pr_pref)) in 
    }
    all matched_pr: (m.matching).Recevier | {
        matched_rx: Proposer.(m.matching) | {

        }
    }



}