AttachSpec("../CHIMP/CHIMP.spec"); // for NumberFieldExtra and AlgebraizeElementExtra
import "stark_unit.m" : StarkE;

// Magma has troubles with impriimitive characters,
// so we work it out here
function lfunc_der(chi, CC)
    chi0 := AssociatedPrimitiveCharacter(chi);
    Lchi0 := LSeries(chi0 : Precision := Precision(CC));
    m := Modulus(chi);
    f := Modulus(chi0);
    // prime divisors of m that do not divide f
    ps := [p[1] : p in Factorization(m div (m + f))];
    // Here, P = prod_{p in ps} (1 - chi0(p)Np^(-s))
    // so that P(0) = prod_{p in ps} (1 - chi0(p))
    // and P'(0) = sum_{p in ps} prod_{q ne p} (1 - chi0(q)) chi0(p) log(Np)
    P0 := &*[CC | 1 - chi0(p) : p in ps];
    P0_der := &+[CC | &*[CC | 1 - chi0(q) : q in ps | q ne p]*(CC!chi0(p))*Log(CC!Norm(p)) : p in ps];
    // if chi0 is trivial, L*(s) has poles and we need to be careful
    O := Order(f);
    if f eq 1*O then
        h := ClassNumber(O);
        w := #UnitGroup(O);
        val0 := -h/w;
        der0 := 0;
    else
        val0 := Evaluate(Lchi0, 0);
        der0 := Evaluate(Lchi0, 0 : Derivative := 1);
    end if;
    return P0*der0 + P0_der*val0;
end function;

// test for an abelian extension of an imaginary quadratic
// B is the norm bound to test reciprocity
procedure testStarkUnit(K : prec := Precision(GetDefaultRealField()), B := 100)
  F := BaseField(K);
  // Verifying that F is imaginary quadratic
  QQ := Rationals();
  assert Degree(F) eq 2;
  assert BaseField(F) eq QQ;
  r, s := Signature(F);
  assert (r eq 0) and (s eq 1);
  // verifying that K is an abelian extension of F
  assert IsAbelian(K);
  AK := AbelianExtension(K);
  frakf := Conductor(AK);
  rcgf, m_rcgf := RayClassGroup(frakf);
  nm_gp_map := NormGroup(AK);
  nm_gp := Domain(nm_gp_map);
  quo := hom<rcgf -> nm_gp | [m_rcgf(rcgf.i)@@nm_gp_map : i in [1..Ngens(rcgf)]]>;
  J := Kernel(quo);
  // gens := [nm_gp_map(x)@@m_rcgf : x in Generators(nm_gp)];
  // J := sub<rcgf | gens>;
  J_idls := [m_rcgf(j) : j in J];
  coset_reps := Transversal(rcgf, J);
  UF, mUF := UnitGroup(F);
  w_frakf := #[u : u in UF | mUF(u) - 1 in frakf];
  f := Minimum(frakf);
  CC<i> := ComplexField(prec);
  has_root, root := HasRoot(DefiningPolynomial(K), CC);
  assert has_root;
  emb_CC := hom<K -> CC | root>;
  // checking Stark's equation holds for all chi in X
  // Not sure what is the correct precision bound
  E := AssociativeArray();
  for c in coset_reps do
    E[c] := StarkE(m_rcgf(c),frakf, emb_CC, J_idls);
  end for;
  eps := 10^((-prec + 2) div Degree(K));
  // X := HeckeCharacterGroup(frakf);
  X := HeckeCharacterGroup(AK);
  for chi in Elements(X) do
    unit_eqn := -1/(6*f*w_frakf) * &+[(CC!chi(m_rcgf(c)))*Log(AbsoluteValue(E[c])) : c in coset_reps];
    Lvalue := lfunc_der(chi, CC);
    print Abs(Lvalue - unit_eqn);
    assert Abs(Lvalue - unit_eqn) lt eps;
  end for;
  // Testing the E(c) are algebraic integers in K
  E_alg := AssociativeArray();
  Kabs := AbsoluteField(K);
  _, K_to_Kabs := IsIsomorphic(K, Kabs);
  Kextra, root := NumberFieldExtra(DefiningPolynomial(Kabs) : prec := prec);
  Kabs_to_Kextra := hom<Kabs -> Kextra | root>;
  K_to_Kextra := K_to_Kabs * Kabs_to_Kextra;
  starks := [E[c] : c in coset_reps];
  in_K, starks_alg := AlgebraizeElementsExtra(starks, Kextra);
  error if not in_K, "Could not find element in K, please increase precision!";
  for i->c in coset_reps do
    // in_K, E_alg[c] := AlgebraizeElementExtra(E[c], Kextra);
    E_alg[c] := starks_alg[i];
    assert IsIntegral(E_alg[c]);
  end for;
  B := 100;
  ps := [p : p in PrimesUpTo(B, F : coprime_to := frakf) | IsSplit(p)];
  ps_Kextra := [&+[K_to_Kextra(b)*Integers(Kextra) : b in Basis(p)] : p in ps];
  // Testing reciprocity
  assert &and[&and[E_alg[c]^Norm(ps[i]) - E_alg[(m_rcgf(c)*ps[i])@@m_rcgf] in p : c in coset_reps] : i->p in ps_Kextra];
end procedure;

// testing a cyclotomic field extension
F := CyclotomicField(3);
K := CyclotomicField(12);
testStarkUnit(RelativeField(F,K) : prec := 100);
// testing the same
Fx<x> := PolynomialRing(F);
K := ext<F | x^2 + 1>;
testStarkUnit(K : prec := 100);
// testing a quadratic extension which is not a ray 
// class field
K := ext<F | x^2 - 2>;
testStarkUnit(K : prec := 200);