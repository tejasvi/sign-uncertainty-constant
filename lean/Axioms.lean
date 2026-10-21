import SignUnc.ProbeK

/-! Prints the statements of the lower bound, the upper bound and Theorem 1.1, the probe of the named hypothesis
`ExtremizerHyp`, and the axioms of the theorems shipped here: `lake env lean Axioms.lean`.  Each of them depends only
on `propext`, `Classical.choice` and `Quot.sound`. -/

#check @SignUnc.lower_weakK
#print SignUnc.LowerStatementWeak
#check @SignUnc.lower_strictK
#print SignUnc.ExtremizerHyp
#check @SignUnc.mainK
#print SignUnc.MainStatement
#check @SignUnc.upperK
#print SignUnc.UpperStatement
#check @SignUnc.A_pos_classA
#check @SignUnc.A_ft_pos_classA
#check @SignUnc.A_pos_class611
#check @SignUnc.A_ft_pos_class611
#check @SignUnc.aplus2_pos_finiteK
#check @SignUnc.probe_clauses
#check @SignUnc.probe_le
#print axioms SignUnc.A_pos_classA
#print axioms SignUnc.A_ft_pos_classA
#print axioms SignUnc.A_pos_class611
#print axioms SignUnc.A_ft_pos_class611
#print axioms SignUnc.lower_weakK
#print axioms SignUnc.lower_strictK
#print axioms SignUnc.mainK
#print axioms SignUnc.upperK
#print axioms SignUnc.aplus2_pos_finiteK
#print axioms SignUnc.probe_clauses
#print axioms SignUnc.probe_le
