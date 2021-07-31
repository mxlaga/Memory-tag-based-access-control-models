/* Policy
 * Author: Veronica
 * Creation date: 2021/5/6
 */
MACHINE
    Policy
SEES
    Tag
SETS
    OP = { Read,Write,Exe,Nop }
VARIABLES
    ac_policy,up_policy
INVARIANT
    ac_policy ⊆ TAG * TAG * OP ∧
    up_policy ⊆ TAG *  TAG
INITIALISATION
    ac_policy ,up_policy:= {} ,{}
OPERATIONS
    Create_Ac_Policy =
    BEGIN
        ac_policy := ac_policy ∪ {NU ↦ NU ↦ Read,NU ↦ NU ↦ Write,NU ↦ NU ↦ Exe,
                                  NS ↦ NU ↦ Read,NS ↦ NU ↦ Write,
                                  NS ↦ NS ↦ Read,NS ↦ NS ↦ Write,NS ↦ NS ↦ Exe,
                                  TU ↦ NU ↦ Read,TU ↦ NU ↦ Write,
                                  TU ↦ NS ↦ Read,TU ↦ NS ↦ Write,
                                  TU ↦ TU ↦ Read,TU ↦ TU ↦ Write,TU ↦ TU ↦ Exe,
                                  TS ↦ NU ↦ Read,TS ↦ NU ↦ Write,
                                  TS ↦ NS ↦ Read,TS ↦ NS ↦ Write,
                                  TS ↦ TU ↦ Read,TS ↦ TU ↦ Write,
                                  TS ↦ TS ↦ Read,TS ↦ TS ↦ Write,TS ↦ TS ↦ Exe}
    END;
    
    Create_Up_Policy =
    BEGIN
        up_policy := up_policy ∪ {NU ↦ NU,
                                          NS ↦ NU,NS ↦ NS,
                                          TU ↦ NU,TU ↦ NS,TU ↦ TU,
                                          TS ↦ NU,TS ↦ NS,TS ↦ TU,TS ↦ TS}
    END
END
