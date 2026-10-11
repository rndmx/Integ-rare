/-
Census: kernel-checked certificates for the regions of a 4-set at pattern 0, one per
unit-permutation orbit of realized profiles (Theorem E, rate `3.8733`).
-/
import IIT.Census.CertDataBase

namespace IIT
namespace Census

set_option maxRecDepth 100000

/-- Gordan certificate for the region of profile 0. -/
def cd_k4_0 : cd_GCert :=
  { C0 := [[false, false, false, true], [false, false, false, true], [false, false, false, true], [true, true, true, false]],
    r0 := cd_Row.min [0, 0, 0, 3] [0, 0, 0, 1], w0 := 1,
    rows := [(cd_Row.min [0, 0, 0, 3] [1, 0, 0, 0], 1)] }

theorem cd_k4_0_ok : cd_checkG 4 cd_k4_0 = true := by decide +kernel

theorem cd_k4_0_cov : cd_Covered 4 38733 10000 cd_k4_0.C0 := Or.inr ⟨cd_k4_0, rfl, cd_k4_0_ok⟩

/-- Half-space certificate for the region of profile 1. -/
def cd_k4_1 : cd_Cert :=
  { C0 := [[false, false, false, true], [false, false, false, true], [false, false, false, true], [false, false, false, false]],
    rows := [(cd_Row.min [0, 1, 2, 3] [0, 0, 0, 0], 18801145), (cd_Row.min [0, 1, 2, 3] [0, 0, 0, 1], 11192343)],
    wF := 268435456,
    v := [796451528, 0, -179960928, 0, -179960928, 0, -179960928, 0, 283314040, 0, -179960928, 0, -179960928, 0, -179960928, 0, 796451528, -179960928, 0, 0, -179960928, -179960928, 0, 0, 283314040, -179960928, 0, 0, -179960928, -179960928, 0, 0, 796451528, -179960928, -179960928, -179960928, 0, 0, 0, 0, 283314040, -179960928, -179960928, -179960928, 0, 0, 0, 0, 789648090, -112806870, -112806870, -112806870, -112806870, -112806870, -112806870, -112806870, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem cd_k4_1_ok : cd_check 4 cd_k4_1 38733 10000 = true := by decide +kernel

theorem cd_k4_1_cov : cd_Covered 4 38733 10000 cd_k4_1.C0 := Or.inl ⟨cd_k4_1, rfl, cd_k4_1_ok⟩

/-- Half-space certificate for the region of profile 2. -/
def cd_k4_2 : cd_Cert :=
  { C0 := [[false, false, false, false], [false, false, false, false], [false, false, false, false], [true, true, true, false]],
    rows := [(cd_Row.min [0, 1, 2, 3] [0, 0, 0, 0], 89478485)],
    wF := 1073741824,
    v := [3758096370, 0, -536870910, 0, -536870910, 0, -536870910, 0, -536870910, 0, -536870910, 0, -536870910, 0, -536870910, 0, 3758096370, -536870910, 0, 0, -536870910, -536870910, 0, 0, -536870910, -536870910, 0, 0, -536870910, -536870910, 0, 0, 3758096370, -536870910, -536870910, -536870910, 0, 0, 0, 0, -536870910, -536870910, -536870910, -536870910, 0, 0, 0, 0, 3758096426, -536870918, -536870918, -536870918, -536870918, -536870918, -536870918, -536870918, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem cd_k4_2_ok : cd_check 4 cd_k4_2 38733 10000 = true := by decide +kernel

theorem cd_k4_2_cov : cd_Covered 4 38733 10000 cd_k4_2.C0 := Or.inl ⟨cd_k4_2, rfl, cd_k4_2_ok⟩

/-- Gordan certificate for the region of profile 3. -/
def cd_k4_3 : cd_GCert :=
  { C0 := [[false, false, true, true], [false, false, true, true], [true, true, false, false], [true, true, false, false]],
    r0 := cd_Row.min [0, 0, 2, 2] [0, 0, 1, 0], w0 := 1,
    rows := [(cd_Row.min [0, 0, 2, 2] [1, 0, 0, 0], 1)] }

theorem cd_k4_3_ok : cd_checkG 4 cd_k4_3 = true := by decide +kernel

theorem cd_k4_3_cov : cd_Covered 4 38733 10000 cd_k4_3.C0 := Or.inr ⟨cd_k4_3, rfl, cd_k4_3_ok⟩

/-- Half-space certificate for the region of profile 4. -/
def cd_k4_4 : cd_Cert :=
  { C0 := [[false, false, true, true], [false, false, true, true], [false, false, false, false], [false, false, false, false]],
    rows := [(cd_Row.min [0, 1, 2, 2] [0, 0, 1, 0], 57037482), (cd_Row.min [0, 1, 2, 3] [0, 0, 0, 0], 38300019)],
    wF := 536870912,
    v := [2159449560, 0, -762700008, 0, 297116824, 0, -762700008, 0, 297116824, 0, -762700008, 0, 297116824, 0, -762700008, 0, 2159449560, -762700008, 0, 0, 297116824, -762700008, 0, 0, 297116824, -762700008, 0, 0, 297116824, -762700008, 0, 0, 2144801064, -306400152, -306400152, -306400152, 0, 0, 0, 0, -306400152, -306400152, -306400152, -306400152, 0, 0, 0, 0, 2144801064, -306400152, -306400152, -306400152, -306400152, -306400152, -306400152, -306400152, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem cd_k4_4_ok : cd_check 4 cd_k4_4 38733 10000 = true := by decide +kernel

theorem cd_k4_4_cov : cd_Covered 4 38733 10000 cd_k4_4.C0 := Or.inl ⟨cd_k4_4, rfl, cd_k4_4_ok⟩

/-- Gordan certificate for the region of profile 5. -/
def cd_k4_5 : cd_GCert :=
  { C0 := [[false, false, true, true], [false, false, true, true], [true, true, false, true], [true, true, true, false]],
    r0 := cd_Row.min [0, 0, 0, 3] [1, 0, 0, 0], w0 := 1,
    rows := [(cd_Row.min [0, 0, 2, 3] [0, 0, 0, 1], 1)] }

theorem cd_k4_5_ok : cd_checkG 4 cd_k4_5 = true := by decide +kernel

theorem cd_k4_5_cov : cd_Covered 4 38733 10000 cd_k4_5.C0 := Or.inr ⟨cd_k4_5, rfl, cd_k4_5_ok⟩

/-- Gordan certificate for the region of profile 6. -/
def cd_k4_6 : cd_GCert :=
  { C0 := [[false, false, true, true], [false, false, true, true], [true, true, false, true], [false, false, false, false]],
    r0 := cd_Row.min [0, 0, 2, 0] [1, 0, 0, 0], w0 := 1,
    rows := [(cd_Row.min [0, 0, 2, 2] [0, 0, 1, 0], 1)] }

theorem cd_k4_6_ok : cd_checkG 4 cd_k4_6 = true := by decide +kernel

theorem cd_k4_6_cov : cd_Covered 4 38733 10000 cd_k4_6.C0 := Or.inr ⟨cd_k4_6, rfl, cd_k4_6_ok⟩

/-- Half-space certificate for the region of profile 7. -/
def cd_k4_7 : cd_Cert :=
  { C0 := [[false, false, true, true], [false, false, true, true], [false, false, false, true], [false, false, true, false]],
    rows := [(cd_Row.min [0, 1, 2, 2] [0, 0, 1, 0], 15657633), (cd_Row.min [0, 1, 2, 3] [0, 0, 0, 0], 111094344), (cd_Row.min [0, 1, 2, 3] [0, 0, 1, 1], 42428823)],
    wF := 1073741824,
    v := [5897986968, 0, -2030169600, 0, 740897144, 0, -2030169600, 0, 740897144, 0, -2030169600, 0, 740897144, 0, -2030169600, 0, 5897986968, -2030169600, 0, 0, 740897144, -2030169600, 0, 0, 740897144, -2030169600, 0, 0, 740897144, -2030169600, 0, 0, 5826374912, -1333132128, -1333132128, -1333132128, 0, 0, 0, 0, 2172417856, -1333132128, -1333132128, -1333132128, 0, 0, 0, 0, 5826374912, -1333132128, -1333132128, -1333132128, 2172417856, -1333132128, -1333132128, -1333132128, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem cd_k4_7_ok : cd_check 4 cd_k4_7 38733 10000 = true := by decide +kernel

theorem cd_k4_7_cov : cd_Covered 4 38733 10000 cd_k4_7.C0 := Or.inl ⟨cd_k4_7, rfl, cd_k4_7_ok⟩

/-- Half-space certificate for the region of profile 8. -/
def cd_k4_8 : cd_Cert :=
  { C0 := [[false, false, true, true], [false, false, true, true], [false, false, false, true], [true, true, true, false]],
    rows := [(cd_Row.min [0, 0, 2, 3] [1, 0, 0, 0], 16894859), (cd_Row.min [0, 1, 2, 3] [0, 0, 0, 0], 99818029), (cd_Row.min [0, 1, 2, 3] [0, 0, 1, 0], 32781103), (cd_Row.min [0, 1, 2, 3] [0, 0, 1, 2], 46781033)],
    wF := 1073741824,
    v := [8231171260, 0, -2870082640, 0, 1083053100, 0, -2870082640, 0, 1083053100, 0, -2870082640, 0, 1083053100, 0, -2870082640, 0, 8231171260, -2870082640, 0, 0, 1083053100, -2870082640, 0, 0, 1083053100, -2870082640, 0, 0, 1083053100, -2870082640, 0, 0, 8159558088, -1867406208, -1867406208, -1867406208, 0, 0, 0, 0, 3044879160, -1867406208, -1867406208, -1867406208, 0, 0, 0, 0, 8146827598, -1163832514, -1163832514, -1163832514, -1163832514, -1163832514, -1163832514, -1163832514, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem cd_k4_8_ok : cd_check 4 cd_k4_8 38733 10000 = true := by decide +kernel

theorem cd_k4_8_cov : cd_Covered 4 38733 10000 cd_k4_8.C0 := Or.inl ⟨cd_k4_8, rfl, cd_k4_8_ok⟩

/-- Gordan certificate for the region of profile 9. -/
def cd_k4_9 : cd_GCert :=
  { C0 := [[false, false, false, false], [false, false, false, false], [true, true, false, true], [true, true, true, false]],
    r0 := cd_Row.min [0, 0, 0, 3] [1, 0, 0, 0], w0 := 1,
    rows := [(cd_Row.min [0, 0, 2, 0] [1, 0, 0, 0], 1)] }

theorem cd_k4_9_ok : cd_checkG 4 cd_k4_9 = true := by decide +kernel

theorem cd_k4_9_cov : cd_Covered 4 38733 10000 cd_k4_9.C0 := Or.inr ⟨cd_k4_9, rfl, cd_k4_9_ok⟩

/-- Half-space certificate for the region of profile 10. -/
def cd_k4_10 : cd_Cert :=
  { C0 := [[false, false, false, true], [false, false, false, true], [true, true, false, true], [true, true, false, false]],
    rows := [(cd_Row.min [0, 0, 2, 3] [1, 0, 0, 0], 24385815), (cd_Row.min [0, 0, 2, 3] [1, 0, 0, 2], 52121377), (cd_Row.min [0, 1, 2, 0] [1, 0, 0, 0], 9780136), (cd_Row.min [0, 1, 2, 1] [0, 1, 0, 0], 9780136), (cd_Row.min [0, 1, 2, 3] [0, 0, 0, 0], 108841753)],
    wF := 1073741824,
    v := [7239688234, 0, -1660706446, 0, -1660706446, 0, -1660706446, 0, 2724550442, 0, -1660706446, 0, -1660706446, 0, -1660706446, 0, 7239688234, -1660706446, 0, 0, -1660706446, -1660706446, 0, 0, 2724550442, -1660706446, 0, 0, -1660706446, -1660706446, 0, 0, 7299008766, -1042715538, -1042715538, -1042715538, 0, 0, 0, 0, -1042715538, -1042715538, -1042715538, -1042715538, 0, 0, 0, 0, 7208115610, 1057141770, 1057141770, 1057141770, -2594885230, -2594885230, -2594885230, -2594885230, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem cd_k4_10_ok : cd_check 4 cd_k4_10 38733 10000 = true := by decide +kernel

theorem cd_k4_10_cov : cd_Covered 4 38733 10000 cd_k4_10.C0 := Or.inl ⟨cd_k4_10, rfl, cd_k4_10_ok⟩

/-- Half-space certificate for the region of profile 11. -/
def cd_k4_11 : cd_Cert :=
  { C0 := [[false, false, false, true], [false, false, false, true], [true, true, false, true], [true, true, true, false]],
    rows := [(cd_Row.min [0, 0, 2, 3] [1, 0, 0, 0], 36018153), (cd_Row.min [0, 1, 2, 0] [1, 0, 0, 0], 291409), (cd_Row.min [0, 1, 2, 1] [0, 1, 0, 0], 291409), (cd_Row.min [0, 1, 2, 3] [0, 0, 0, 0], 127400510)],
    wF := 1073741824,
    v := [8904133952, 0, -2043070704, 0, -2043070704, 0, -2043070704, 0, 3354290272, 0, -2043070704, 0, -2043070704, 0, -2043070704, 0, 8904133952, -2043070704, 0, 0, -2043070704, -2043070704, 0, 0, 3354290272, -2043070704, 0, 0, -2043070704, -2043070704, 0, 0, 8922784164, -1274683452, -1274683452, -1274683452, 0, 0, 0, 0, -1274683452, -1274683452, -1274683452, -1274683452, 0, 0, 0, 0, 8857508548, -1265358364, -1265358364, -1265358364, -1265358364, -1265358364, -1265358364, -1265358364, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem cd_k4_11_ok : cd_check 4 cd_k4_11 38733 10000 = true := by decide +kernel

theorem cd_k4_11_cov : cd_Covered 4 38733 10000 cd_k4_11.C0 := Or.inl ⟨cd_k4_11, rfl, cd_k4_11_ok⟩

/-- Half-space certificate for the region of profile 12. -/
def cd_k4_12 : cd_Cert :=
  { C0 := [[false, false, true, true], [false, false, true, true], [true, true, false, true], [true, true, false, false]],
    rows := [(cd_Row.min [0, 0, 2, 0] [1, 0, 0, 0], 17699636), (cd_Row.min [0, 0, 2, 3] [0, 0, 0, 0], 3237204), (cd_Row.min [0, 0, 2, 3] [0, 0, 0, 1], 1037857), (cd_Row.min [0, 1, 2, 3] [0, 0, 0, 0], 178124252)],
    wF := 1073741824,
    v := [9027540576, 0, -3206236536, 0, 1265801856, 0, -3206236536, 0, 1265801856, 0, -3206236536, 0, 1265801856, 0, -3206236536, 0, 9027540576, -3206236536, 0, 0, 1265801856, -3206236536, 0, 0, 1265801856, -3206236536, 0, 0, 1265801856, -3206236536, 0, 0, 9021675516, -1288810788, -1288810788, -1288810788, 0, 0, 0, 0, -1288810788, -1288810788, -1288810788, -1288810788, 0, 0, 0, 0, 8973721692, 1361434380, 1361434380, 1361434380, -3264506208, -3264506208, -3264506208, -3264506208, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem cd_k4_12_ok : cd_check 4 cd_k4_12 38733 10000 = true := by decide +kernel

theorem cd_k4_12_cov : cd_Covered 4 38733 10000 cd_k4_12.C0 := Or.inl ⟨cd_k4_12, rfl, cd_k4_12_ok⟩

/-- Gordan certificate for the region of profile 13. -/
def cd_k4_13 : cd_GCert :=
  { C0 := [[false, true, true, true], [true, false, true, true], [true, true, false, true], [true, true, true, false]],
    r0 := cd_Row.min [0, 0, 2, 3] [1, 0, 0, 0], w0 := 1,
    rows := [(cd_Row.min [0, 1, 2, 3] [0, 0, 0, 1], 1), (cd_Row.min [0, 1, 2, 3] [0, 0, 1, 0], 1)] }

theorem cd_k4_13_ok : cd_checkG 4 cd_k4_13 = true := by decide +kernel

theorem cd_k4_13_cov : cd_Covered 4 38733 10000 cd_k4_13.C0 := Or.inr ⟨cd_k4_13, rfl, cd_k4_13_ok⟩

/-- Gordan certificate for the region of profile 14. -/
def cd_k4_14 : cd_GCert :=
  { C0 := [[false, true, true, true], [true, false, true, true], [true, true, false, true], [false, false, false, false]],
    r0 := cd_Row.min [0, 0, 2, 0] [1, 0, 0, 0], w0 := 1,
    rows := [(cd_Row.min [0, 1, 2, 2] [0, 0, 1, 0], 1)] }

theorem cd_k4_14_ok : cd_checkG 4 cd_k4_14 = true := by decide +kernel

theorem cd_k4_14_cov : cd_Covered 4 38733 10000 cd_k4_14.C0 := Or.inr ⟨cd_k4_14, rfl, cd_k4_14_ok⟩

/-- Half-space certificate for the region of profile 15. -/
def cd_k4_15 : cd_Cert :=
  { C0 := [[false, true, true, true], [true, false, true, true], [false, false, false, true], [false, false, true, false]],
    rows := [(cd_Row.min [0, 1, 2, 2] [0, 0, 1, 0], 37843976), (cd_Row.min [0, 1, 2, 3] [0, 0, 0, 0], 128688379)],
    wF := 1073741824,
    v := [8885467640, 0, -1269352520, 0, -1269352520, 0, -1269352520, 0, -1269352520, 0, -1269352520, 0, -1269352520, 0, -1269352520, 0, 8885467640, -1269352520, 0, 0, -1269352520, -1269352520, 0, 0, -1269352520, -1269352520, 0, 0, -1269352520, -1269352520, 0, 0, 8832437808, -2059014064, -2059014064, -2059014064, 0, 0, 0, 0, 3521646576, -2059014064, -2059014064, -2059014064, 0, 0, 0, 0, 8832437808, -2059014064, -2059014064, -2059014064, 3521646576, -2059014064, -2059014064, -2059014064, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem cd_k4_15_ok : cd_check 4 cd_k4_15 38733 10000 = true := by decide +kernel

theorem cd_k4_15_cov : cd_Covered 4 38733 10000 cd_k4_15.C0 := Or.inl ⟨cd_k4_15, rfl, cd_k4_15_ok⟩

/-- Half-space certificate for the region of profile 16. -/
def cd_k4_16 : cd_Cert :=
  { C0 := [[false, true, true, true], [true, false, true, true], [false, false, false, true], [true, true, true, false]],
    rows := [(cd_Row.min [0, 1, 2, 3] [0, 0, 0, 0], 136657164), (cd_Row.min [0, 1, 2, 3] [0, 0, 0, 1], 321016), (cd_Row.min [0, 1, 2, 3] [0, 0, 1, 0], 39998617)],
    wF := 1073741824,
    v := [11770459806, 0, -1681494258, 0, -1681494258, 0, -1681494258, 0, -1681494258, 0, -1681494258, 0, -1681494258, 0, -1681494258, 0, 11770459806, -1681494258, 0, 0, -1681494258, -1681494258, 0, 0, -1681494258, -1681494258, 0, 0, -1681494258, -1681494258, 0, 0, 11744778472, -2739563600, -2739563600, -2739563600, 0, 0, 0, 0, 4692603128, -2739563600, -2739563600, -2739563600, 0, 0, 0, 0, 11725517566, -1675073938, -1675073938, -1675073938, -1675073938, -1675073938, -1675073938, -1675073938, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem cd_k4_16_ok : cd_check 4 cd_k4_16 38733 10000 = true := by decide +kernel

theorem cd_k4_16_cov : cd_Covered 4 38733 10000 cd_k4_16.C0 := Or.inl ⟨cd_k4_16, rfl, cd_k4_16_ok⟩

/-- Half-space certificate for the region of profile 17. -/
def cd_k4_17 : cd_Cert :=
  { C0 := [[false, true, true, true], [false, false, true, true], [false, true, false, true], [false, true, true, false]],
    rows := [(cd_Row.min [0, 1, 1, 1] [0, 1, 0, 0], 18730627), (cd_Row.min [0, 1, 2, 3] [0, 0, 0, 0], 176775073)],
    wF := 1073741824,
    v := [9181205138, 0, -1311600734, 0, -1311600734, 0, -1311600734, 0, -1311600734, 0, -1311600734, 0, -1311600734, 0, -1311600734, 0, 9028648002, -3181951314, 0, 0, 1233052418, -3181951314, 0, 0, 1233052418, -3181951314, 0, 0, 1233052418, -3181951314, 0, 0, 9028648002, -3181951314, 1233052418, -3181951314, 0, 0, 0, 0, 1233052418, -3181951314, 1233052418, -3181951314, 0, 0, 0, 0, 9028648002, -3181951314, 1233052418, -3181951314, 1233052418, -3181951314, 1233052418, -3181951314, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem cd_k4_17_ok : cd_check 4 cd_k4_17 38733 10000 = true := by decide +kernel

theorem cd_k4_17_cov : cd_Covered 4 38733 10000 cd_k4_17.C0 := Or.inl ⟨cd_k4_17, rfl, cd_k4_17_ok⟩

/-- Half-space certificate for the region of profile 18. -/
def cd_k4_18 : cd_Cert :=
  { C0 := [[false, true, true, true], [false, false, true, true], [false, true, false, true], [true, true, true, false]],
    rows := [(cd_Row.min [0, 1, 1, 3] [0, 1, 0, 0], 19444137), (cd_Row.min [0, 1, 2, 1] [0, 1, 0, 0], 460762), (cd_Row.min [0, 1, 2, 2] [0, 0, 1, 0], 460762), (cd_Row.min [0, 1, 2, 3] [0, 0, 0, 0], 190415979)],
    wF := 1073741824,
    v := [10841215140, 0, -1548745020, 0, -1548745020, 0, -1548745020, 0, -1548745020, 0, -1548745020, 0, -1548745020, 0, -1548745020, 0, 10721417060, -3817534820, 0, 0, 1516240740, -3817534820, 0, 0, 1516240740, -3817534820, 0, 0, 1516240740, -3817534820, 0, 0, 10721417060, -3817534820, 1516240740, -3817534820, 0, 0, 0, 0, 1516240740, -3817534820, 1516240740, -3817534820, 0, 0, 0, 0, 10712201780, -1530314540, -1530314540, -1530314540, -1530314540, -1530314540, -1530314540, -1530314540, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem cd_k4_18_ok : cd_check 4 cd_k4_18 38733 10000 = true := by decide +kernel

theorem cd_k4_18_cov : cd_Covered 4 38733 10000 cd_k4_18.C0 := Or.inl ⟨cd_k4_18, rfl, cd_k4_18_ok⟩

/-- Half-space certificate for the region of profile 19. -/
def cd_k4_19 : cd_Cert :=
  { C0 := [[false, true, true, true], [false, false, true, true], [true, true, false, true], [true, true, true, false]],
    rows := [(cd_Row.min [0, 1, 2, 2] [0, 0, 1, 0], 504829), (cd_Row.min [0, 1, 2, 3] [0, 0, 0, 0], 207170963), (cd_Row.min [0, 1, 2, 3] [0, 1, 0, 0], 21303786)],
    wF := 1073741824,
    v := [12763836092, 0, -1823405156, 0, -1823405156, 0, -1823405156, 0, -1823405156, 0, -1823405156, 0, -1823405156, 0, -1823405156, 0, 12697198608, -4568867424, 0, 0, 1859423696, -4568867424, 0, 0, 1859423696, -4568867424, 0, 0, 1859423696, -4568867424, 0, 0, 12686092426, -1812298918, -1812298918, -1812298918, 0, 0, 0, 0, -1812298918, -1812298918, -1812298918, -1812298918, 0, 0, 0, 0, 12686092426, -1812298918, -1812298918, -1812298918, -1812298918, -1812298918, -1812298918, -1812298918, 0, 0, 0, 0, 0, 0, 0, 0] }

theorem cd_k4_19_ok : cd_check 4 cd_k4_19 38733 10000 = true := by decide +kernel

theorem cd_k4_19_cov : cd_Covered 4 38733 10000 cd_k4_19.C0 := Or.inl ⟨cd_k4_19, rfl, cd_k4_19_ok⟩

/-- The certified profiles. -/
def cd_k4_list : List (List (List Bool)) := [cd_k4_0.C0, cd_k4_1.C0, cd_k4_2.C0, cd_k4_3.C0, cd_k4_4.C0, cd_k4_5.C0, cd_k4_6.C0, cd_k4_7.C0, cd_k4_8.C0, cd_k4_9.C0, cd_k4_10.C0, cd_k4_11.C0, cd_k4_12.C0, cd_k4_13.C0, cd_k4_14.C0, cd_k4_15.C0, cd_k4_16.C0, cd_k4_17.C0, cd_k4_18.C0, cd_k4_19.C0]

/-- Every certified region is covered at rate `38733 / 10000`. -/
theorem cd_k4_covered : ∀ C ∈ cd_k4_list, cd_Covered 4 38733 10000 C := by
  intro C hC
  simp only [cd_k4_list, List.mem_cons, List.not_mem_nil, or_false] at hC
  rcases hC with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact cd_k4_0_cov
  · exact cd_k4_1_cov
  · exact cd_k4_2_cov
  · exact cd_k4_3_cov
  · exact cd_k4_4_cov
  · exact cd_k4_5_cov
  · exact cd_k4_6_cov
  · exact cd_k4_7_cov
  · exact cd_k4_8_cov
  · exact cd_k4_9_cov
  · exact cd_k4_10_cov
  · exact cd_k4_11_cov
  · exact cd_k4_12_cov
  · exact cd_k4_13_cov
  · exact cd_k4_14_cov
  · exact cd_k4_15_cov
  · exact cd_k4_16_cov
  · exact cd_k4_17_cov
  · exact cd_k4_18_cov
  · exact cd_k4_19_cov

end Census
end IIT
