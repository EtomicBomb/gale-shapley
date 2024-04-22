#lang forge/temporal



sig Proposer{
    //only match with people that you prefer
    pref : pfunc Int -> Receiver
}

sig Receiver{
    pref : pfunc Int -> Proposer
}

sig State {
    var unfilled: set Proposer

}

sig Matching{
    var match: pfunc Proposer -> Receiver
}



pred wellformed_matching[m: Matching] {
    all rx: Receiver | lone (~m.matching)[rx]
}

pred wellformed_pref_ranking_for_proposers{
    all p :Proposer|  isSeqOf[p.pref, Receiver]
 
}

pred wellformed_pref_ranking_for_receivers{
    all r :Receiver|  isSeqOf[r.pref, Proposer]
 
}

pred init_state{
    //there is no matching


    
}

pred matching {
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


pred stable{
    --guard
    --there are no two elements who would both prefer each other over their current match
    --action
    
}


pred final_state{
    --guard
    //all proposers are matched?
    stable
    --action
    --no matching
    
}








pred traces{
    init_state
    always wellformed_matching
    always wellformed_pref_ranking_for_proposers
    always wellformed_pref_ranking_for_receivers
    eventually final_state

}

run {
    traces

}

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





https://csci1710.github.io/forge-documentation/forge-standard-library/helpers.html?highlight=sequen#sequence-helpers




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