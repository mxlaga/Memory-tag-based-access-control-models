/* Policy
 * Author: Veronica
 * Creation date: 2021/6/30
 */
MACHINE
    Policy
SEES
    Tag
SETS
    OP = { Read,Write,Exe,Nop }
VARIABLES
    ac_policy,update_policy
INVARIANT
    ac_policy ⊆ TAG * TAG * OP ∧
        update_policy ⊆ TAG *  TAG
INITIALISATION
    ac_policy ,update_policy:= {} ,{}
OPERATIONS
    Create_Ac_Policy(tt,gg,action) =
    PRE
        tt ∈ TAG ∧
        gg ∈ TAG ∧
        action ∈ OP ∧
        tt ↦ gg ↦ action ∉ ac_policy
    THEN
        ac_policy := ac_policy ∪ {tt ↦gg ↦ action}
    END;
    
    Create_Update_Policy(tt,gg) =
    PRE
        tt ∈ TAG ∧
        gg ∈ TAG ∧
        tt ↦ gg ∉ update_policy
    THEN
        update_policy := update_policy ∪ {tt ↦ gg}
    END
END
