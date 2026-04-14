import "stark_unit.m" : StarkE;

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
procedure testStarkUnitRCF(K : prec := Precision(GetDefaultRealField()))
  F := BaseField(K);
  // Verifying that F is imaginary quadratic
  QQ := Rationals();
  assert Degree(F) eq 2;
  assert BaseField(F) eq QQ;
  r, s := Signature(F);
  assert (r eq 0) and (s eq 1);
  // verifying that K is an abelian extension of F
  assert IsAbelian(K);
  frakf := Conductor(AbelianExtension(K));
  rcgf, m_rcgf := RayClassGroup(frakf);
  UF, mUF := UnitGroup(F);
  w_frakf := #[u : u in UF | mUF(u) - 1 in frakf];
  f := Minimum(frakf);
  CC<i> := ComplexField(prec);
  X := HeckeCharacterGroup(frakf);
  // checking Stark's equation holds for all chi in X
  eps := 10^(-10);
  for chi in Elements(X) do
    unit_eqn := -1/(6*f*w_frakf) * &+[(CC!chi(m_rcgf(c)))*Log(AbsoluteValue(StarkE(m_rcgf(c),frakf,CC))) : c in rcgf];
    Lvalue := lfunc_der(chi, CC);
    assert Abs(Lvalue - unit_eqn) lt eps;
  end for;
end procedure;

// test for an abelian extension of an imaginary quadratic
procedure testStarkUnit(K : prec := Precision(GetDefaultRealField()))
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
  // X := HeckeCharacterGroup(frakf);
  X := HeckeCharacterGroup(AK);
  // checking Stark's equation holds for all chi in X
  eps := 10^(-20);
  for chi in Elements(X) do
    unit_eqn := -1/(6*f*w_frakf) * &+[(CC!chi(m_rcgf(c)))*Log(AbsoluteValue(StarkE(m_rcgf(c),frakf,CC, J_idls))) : c in coset_reps];
    Lvalue := lfunc_der(chi, CC);
    print Abs(Lvalue - unit_eqn);
    assert Abs(Lvalue - unit_eqn) lt eps;
  end for;
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
testStarkUnit(K : prec := 100);