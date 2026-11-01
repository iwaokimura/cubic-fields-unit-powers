// c4-regmodel.m --- the regular model of C_4 over Z_2 returned by Magma's
// RegularModel, used in the paper only as an answer key for the model built by
// liu-model-lib.sage / check-c4-l2model.sage (Section 9.5: "This agreement is a
// check, not an input to the proof").
//
// Magma is not free software.  The script runs in the free Magma Online
// Calculator (http://magma.maths.usyd.edu.au/calc/, 60 s limit
// as of 2026-10-31); each call
// below takes well under a second.  Nothing else in this repository needs Magma.
//
// Provenance.  The computation was done on 2026-08-18 (Magma V2.29-9) in five
// calls to the online calculator, and no file of them was kept.  This script
// reconstructs them: the four lines defining C and M2 are verbatim from the
// research log, and the accessor calls are the ones whose output the log
// records.  The script was run as it stands on 2026-10-31 (Magma V2.29-10,
// 0.3 s); its output, in c4-regmodel.out, agrees with the log in every value
// quoted below, including the components of the nine points (2/3 for
// t = 1, -1, -1/11 and 5 for t = -2, 0).
// The output is quoted after each call; check-c4-regmodel.gp records it as data and
// verifies, without Magma, everything about it that can be checked from first
// principles (symmetry, M m = 0, rank 5 with kernel spanned by m, negative
// semidefiniteness, and the component group Z/8 recovered from M itself).
//
// The plane quartic is (eq:quartic) of the paper, w^4 - 6(t-1)^2 w^2 + 27 t (t^3 - 4) = 0,
// homogenised with X = t, Y = w.

P<X,Y,Z> := PolynomialRing(Rationals(), 3);
F := Y^4 - 6*(X-Z)^2*Y^2 + 27*X^4 - 108*X*Z^3;
C := Curve(ProjectiveSpace(P), F);

Genus(C);            // 3
IsNonsingular(C);    // true

M2 := RegularModel(C, 2);
Multiplicities(M2);        // [ 1, 1, 1, 2, 2, 4 ]
IntersectionMatrix(M2);
// [-3  1  0  1  0  0]
// [ 1 -3  0  1  0  0]
// [ 0  0 -4  0  2  0]
// [ 1  1  0 -3  0  1]
// [ 0  0  2  0 -3  1]
// [ 0  0  0  1  1 -1]
ComponentGroup(M2);        // Abelian Group isomorphic to Z/8

// The nine rational points of C_4 (Theorem 9.9), as points of C.
pts := [C | [1,3,1], [1,-3,1], [-1,3,1], [-1,-3,1], [-2,6,1], [-2,-6,1],
            [-1,15,11], [-1,-15,11], [0,0,1]];
for Q in pts do
  PointOnRegularModel(M2, Q);
end for;
// The component indices in these records are local to a patch (each record
// carries a patch index), while Multiplicities and IntersectionMatrix are
// global; E103 found that they cannot be compared across points without
// matching the patches, and the paper does not use them.

// What does not work, for the record (E103):
//   * RegularModel on the AFFINE quartic fails: "Bad affine curve (there are
//     nonregular points at infinity on the special fibre)".  The projective
//     curve above is accepted.
//   * RegularModel(C, 3) fails: "Extending the base field to Number Field with
//     defining polynomial x^2+2x+2", then "Fibre blowups over number fields not
//     yet implemented".  The singular point of the special fibre at 3 is defined
//     over F_9.  The model at 3 used in the paper comes from Dokchitser's
//     Newton-polytope construction instead (check-c4-dv3.sage).
