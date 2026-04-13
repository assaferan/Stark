
// This function returns the polynmoial f described in A.1, together with beta
function AlgebraicPolynomial()
  _<x> := PolynomialRing(Rationals());
  k<beta> := NumberField(x^3 - x^2 + 5*x + 1);
  assert ClassNumber(k) eq 3;
  assert Discriminant(Integers(k)) eq -588;
  H := HilbertClassField(k);
  Q7<zeta7> := CyclotomicField(7);
  Q7plus<lambda7> := sub<Q7 | zeta7 + zeta7^(-1)>;
  k7plus := Compositum(Q7plus, k);
  assert IsIsomorphic(k7plus, H);
  Q3<zeta3> := CyclotomicField(3);
  K := CompositeFields(Q3, H)[1];
  _<x> := PolynomialRing(K);
  f := x^6 - (beta^2 - 4*beta + 1)*x^5 + (-7*beta^2 + 10*beta + 5)*x^4 - 
       (22*beta^2 + 17*beta + 6)*x^3 + (-7*beta^2 + 10*beta + 5)*x^2 -
       (beta^2 - 4*beta + 1)*x + 1;
  return f, beta;
end function;

// This functions creates a complex polynomial corresponding to f
// under an emebdding of the number field into C that sends beta to a real root
function AnalyticPolynomial(f, beta : prec := Precision(GetDefaultRealField()))
  K := BaseRing(f);
  CC<i> := ComplexField(prec);
  // Here we choose an embdding of K into CC 
  roots := [r[1] : r in Roots(DefiningPolynomial(K),CC)];
  embs := [hom<K -> CC | r> : r in roots];
  // Here also lt 1 will work, as the complex roots have imaginary part ~ 2.2
  assert exists(h){h : h in embs | Abs(Im(h(beta))) lt 10^(-prec div 2)};
  CCx<x> := PolynomialRing(CC);
  htilde := hom< Parent(f) -> CCx | h, x>;
  ftilde := htilde(f);
  return ftilde;
end function;

// This function computes the Siegel function Phi(tau,z) (as in A.3)
// taking the product up to the M-th factor
function TruncatedSiegel(tau, z, M)
  CC<i> := Parent(tau);
  assert CC eq Parent(z);
  pi := Pi(CC);
  u := Im(z)/Im(tau);
  assert Abs(Im(z - u*tau)) lt 10^(-Precision(CC) div 2);
  ret := Exp(pi*i*(tau/6 + u*z))*(Exp(pi*i*z) - Exp(-pi*i*z));
  for m in [1..M] do 
    ret *:= (1 - Exp(2*pi*i*(m*tau+z)))*(1-Exp(2*pi*i*(m*tau-z)));
  end for;
  return ret;
end function;

function Siegel_ga(CC, tau, a1, a2, M)
  _<i> := CC;
  pi := Pi(CC);
  ret := -Exp(pi*i*a2*(a1-1));
  q := Exp(2*pi*i*tau);
  B2 := a1^2 - a1 + 1/6;
  ret *:= q^(1/2*B2);
  ret *:= 1 - q^a1 * Exp(2*pi*i*a2);
  for m in [1..M] do
    ret *:= (1 - q^(m+a1)*Exp(2*pi*i*a2))*(1- q^(m-a1)*Exp(-2*pi*i*a2));
  end for;
  return ret;
end function;

// The following computes Phi(tau, (a+b*tau)/7) using product of M terms
function SiegelAt7Torsion(CC, a, b, M)
  _<i> := CC;
  tau := (1 + Sqrt(CC!3)*i)/2;
  z := (a + b*tau)/7;
  return TruncatedSiegel(tau, z, M);
end function;

// computing the c_{a,b} from A.4
// !!! TODO - verify that this is the correct Stickelberger element
function StickelbergerCoefficient(a,b)
  nm := a^2 + a*b + b^2;
  c := nm mod 7;
  return 21 - 6*c;
end function;

// Construct P = \prod Siegel(a,b)^{c_{a,b}} and divide by Siegel(ref)^S,
// S = \sum c_{a,b} (augmentation / kill net weight in the usual Siegel story).
// Do NOT subtract the same constant from every exponent: \prod \Phi^{c_i-k}
// equals P / (\prod \Phi_i)^k, not P / \Phi_ref^{sum c}.
//
// Magnitude: |P / Siegel(ref)^S| = |P| * |Siegel(ref)|^{-S}. If |Siegel(ref)|<1
// and S is large, |Siegel(ref)|^{-S} is enormous (e.g. ref=(0,1), S=252 gives
// ~10^{47} here). If |Siegel(ref)|>1, the ratio can be tiny instead. Until the
// c_{a,b} match the theory for *this* Phi, P and Siegel(ref)^S need not cancel
// in absolute value — only the correct Stickelberger data makes a true unit.
// Optional RefA, RefB: use whatever A.4 fixes; for milder |u| while debugging,
// try a pair with larger |Siegel| (e.g. (2,3) maximizes |Phi| among a,b in [0..6]).
function ConstructUnit(CC, M : RefA := 0, RefB := 1)
  S := &+[StickelbergerCoefficient(a,b) : a,b in [0..6] | a+b gt 0];
  u := &*[SiegelAt7Torsion(CC,a,b,M)^StickelbergerCoefficient(a,b)
	       : a, b in [0..6] | a + b gt 0];
  return u / SiegelAt7Torsion(CC, RefA, RefB, M)^S;
end function;

// Exact roots of f in K = Q(zeta3, H); all have Norm 1 (verified for this f).
// Use this to test Siegel output or to pin ε by the Galois/character rule in A.4
// until ConstructUnit matches the theory (correct Phi, c_{a,b}, 42nd root).
function StarkUnitAlgebraic()
  f, beta := AlgebraicPolynomial();
  K := BaseRing(f);
  return [r[1] : r in Roots(f, K)];
end function;

function StarkUnit(M, prec : bd := 11035, RefA := 0, RefB := 1)
  f, beta := AlgebraicPolynomial();
  f_CC := AnalyticPolynomial(f, beta : prec := prec);
  CC<i> := BaseRing(f_CC);
  u := ConstructUnit(CC, M : RefA := RefA, RefB := RefB);
  u_root := u^(1/42);
  zeta42 := Exp(Pi(CC)*i/21);
  sizes := [Abs(Evaluate(f_CC,u_root*zeta42^k)) : k in [0..41]];
  size, k := Minimum(sizes);
  assert size lt 10^(-bd);
  eps := u_root*zeta42^k;
  return k, eps;
end function;

procedure other_code_I_ran()
  _<x> := PolynomialRing(Rationals());
  k<beta> := NumberField(x^3 - x^2 + 5*x + 1);
  assert ClassNumber(k) eq 3;
  assert Discriminant(Integers(k)) eq -588;
  H := HilbertClassField(k);
  Q7<zeta7> := CyclotomicField(7);
  Q7plus<lambda7> := sub<Q7 | zeta7 + zeta7^(-1)>;
  k7plus := Compositum(Q7plus, k);
  assert IsIsomorphic(k7plus, H);
  Q3<zeta3> := CyclotomicField(3);
  // Denoted F in Robin's notes
  F := Q3;
  K := CompositeFields(Q3, H)[1];
  _<x> := PolynomialRing(K);
  f := x^6 - (beta^2 - 4*beta + 1)*x^5 + (-7*beta^2 + 10*beta + 5)*x^4 -
       (22*beta^2 + 17*beta + 6)*x^3 + (-7*beta^2 + 10*beta + 5)*x^2 -
       (beta^2 - 4*beta + 1)*x + 1;
  // v is the complex place of k;
  assert exists(v){pl : pl in InfinitePlaces(k) | not IsReal(pl)};
  // w is a place of K above v
  assert exists(w){pl : pl in InfinitePlaces(K) | Extends(pl, v)};
  K_over_k := RelativeField(k,K);
  // Disc(K/k) = p3^3
  // p3 is denoted frakp in Robin's notes
  p3 := Factorization(Discriminant(Integers(K_over_k)))[1][1];
  assert Norm(p3) eq 3;
  S := InfinitePlaces(k) cat [Place(p3)];
  p2 := ideal<Integers(k) | [2, beta - 1]>;
  is_isom, k7plus_to_H := IsIsomorphic(k7plus, H);
  assert is_isom;
  L := sub< K | [K | zeta3, k7plus_to_H(lambda7)]>;
  // verifying (*) is satisfied for p2
  assert IsRamified(p2);
  assert IsPrime(2*Integers(L));
  // E = kF
  E := sub< K | zeta3, beta>;
  // verifying E is Galois with Galois group S3
  assert IsNormal(E);
  assert IsIsomorphic(GaloisGroup(E),Sym(3));
  L_has_cc, cc := HasComplexConjugate(L);
  assert L_has_cc;
  // totally real subfield
  Lplus := sub<L | L.1 + cc(L.1)>;
  // K+ = kL+
  Kplus := sub<K | [K!(L.1 + cc(L.1)), beta]>;
  K_over_L := RelativeField(L,K);
  Gal_K_L, _, Gal_K_L_to_aut := AutomorphismGroup(K_over_L);
  eps := 10^(-15);
  for g in Gal_K_L do
    tau := Gal_K_L_to_aut(g);
    found := exists(tau_w){pl : pl in InfinitePlaces(K) | Extends(pl, v) and Abs(Evaluate(K_over_L.1, pl) - Evaluate((K_over_L.1)@@tau, w)) lt eps};
    if not found then
      found := exists(tau_w){pl : pl in InfinitePlaces(K) | Extends(pl, v) and Abs(Evaluate(K_over_L.1, pl) - ComplexConjugate(Evaluate((K_over_L.1)@@tau, w))) lt eps};
    end if;
    if found then break; end if;
  end for;
  K_over_Kplus := RelativeField(Kplus, K);
  K_over_E := RelativeField(E,K);
  Gplus, _, Gplus_to_aut := AutomorphismGroup(K_over_E);
  Gal_K_Kplus, _, Gal_K_Kplus_to_aut := AutomorphismGroup(K_over_Kplus);
  eta := hom<Gal_K_Kplus -> GL(1, Rationals()) | [Matrix([[Sign(Gal_K_Kplus.i)]]) : i in [1..Ngens(Gal_K_Kplus)]]>;
  // !! TODO - this depends on choice of generators, change it
  omega := hom<Gal_K_L -> GL(1,F) | [Matrix([[zeta3^(i-1)]]) : i in [1..Ngens(Gal_K_L)]]>;
  Gal_K_k, _, Gal_K_k_to_aut := AutomorphismGroup(K_over_k);
  // Verifying cyclotomic 
  is_isom, Gal_K_k_to_Z7x := IsIsomorphic(Gal_K_k, GL(1, Integers(7)));
  assert is_isom;
  chars_Z7x := [hom<GL(1,Integers(7)) -> GL(1, Q7) | Matrix([[zeta7^j]])> : j in [0..6]];
  chars_Gal_K_k := [Gal_K_k_to_Z7x * chi : chi in chars_Z7x];
  Gal_L_Q, _, Gal_L_Q_to_aut := AutomorphismGroup(L);
  images_K_k_to_L_Q := [];
  for i in [1..Ngens(Gal_K_k)] do
    assert exists(g){g : g in Gal_L_Q | (Gal_K_k_to_aut(Gal_K_k.i))(L.1) eq Gal_L_Q_to_aut(g)(L.1)};
    Append(~images_K_k_to_L_Q, g);
  end for;
  res_K_k_to_L_Q := hom<Gal_K_k -> Gal_L_Q | images_K_k_to_L_Q>;
  // verify surjective
  assert Image(res_K_k_to_L_Q) eq Gal_L_Q;
  // verify injective
  assert #Kernel(res_K_k_to_L_Q) eq 1;
  E_over_F := RelativeField(F,E);
  Gal_E_F, _, Gal_E_F_to_aut := AutomorphismGroup(E_over_F);
  images_K_L_to_E_F := [];
  for i in [1..Ngens(Gal_K_L)] do
    assert exists(g){g : g in Gal_E_F | (Gal_K_L_to_aut(Gal_K_L.i))(E.1) eq Gal_E_F_to_aut(g)(E.1)};
    Append(~images_K_L_to_E_F, g);
  end for;
  res_K_L_to_E_F := hom<Gal_K_L -> Gal_E_F | images_K_L_to_E_F>;
  assert Image(res_K_L_to_E_F) eq Gal_E_F;
  assert #Kernel(res_K_L_to_E_F) eq 1;
  chi_to_chi_Q := func<chi | res_K_k_to_L_Q^(-1) * chi>;
  omega_F := res_K_L_to_E_F^(-1) * omega;
  L_over_F := RelativeField(F,L);
  Gal_L_F, _, Gal_L_F_to_aut := AutomorphismGroup(L_over_F);
  images_L_F_to_L_Q := [];
  for i in [1..Ngens(Gal_L_F)] do
    assert exists(g){g : g in Gal_L_Q | (Gal_L_F_to_aut(Gal_L_F.i))(L.1) eq Gal_L_Q_to_aut(g)(L.1)};
    Append(~images_L_F_to_L_Q, g);
  end for;
  L_F_to_L_Q := hom<Gal_L_F -> Gal_L_Q | images_L_F_to_L_Q>;
  // some character
  chi := chars_Gal_K_k[3];
  chi_Q := chi_to_chi_Q(chi);
  chi_F :=  L_F_to_L_Q * chi_Q;
  // Denoted G is Robin's notes
  G := Gal_K_k;
  A := AbelianExtension(K_over_k);
  art_A := ArtinMap(A);
  A := NumberField(A);
  _, K_over_k_to_A := IsIsomorphic(K_over_k, A);
  idl_bd := 100;
  idls := IdealsUpTo(idl_bd,k);
  // Choosing only ideals coprime to S
  idls := [a : a in idls | not exists{p : p in Factorization(a) |
	                              Place(p[1]) in S}];
  L_S := func<s, sigma | &+[Norm(a)^(-s) : a in idls |
			  art_A(a)(K_over_k_to_A(K_over_k.1)) eq
			  K_over_k_to_A(Gal_K_k_to_aut(sigma)(K_over_k.1))]>;
  L_S_chi := func<s | &+[chi(sigma)*L_S(s, sigma) : sigma in G]>;
end procedure;

function embed_quad(tau, CC)
  t := CC!Trace(tau);
  n := CC!Norm(tau);
  tau_CC := 1/2*(t+Sqrt(t^2 - 4*n));
  if Im(tau_CC) lt 0 then
    tau_CC := ComplexConjugate(tau_CC);
  end if;
  return tau_CC;
end function;

// Here, a is an ideal in an imaginary quadratic field,
// we find c in Q_>0, tau in H (upper half plane) 
// such that 
// a = c (Z + Z tau)
function find_c_tau(fraka, CC)
  assert ISA(Type(fraka), RngOrdIdl);
  assert Degree(NumberField(Order(fraka))) eq 2;
  c_a := Minimum(fraka);
  // Basis for a
  B := Basis(fraka);
  M := Matrix(Integers(), [Eltseq(bb) : bb in B]);
  // finding a different basis where c_a is a basis element
  a, b := Explode(Eltseq(Solution(M, Vector([c_a,0]))));
  assert a*B[1]+b*B[2] eq c_a;
  // lifting
  g, d, minus_c := XGCD(a,b);
  assert g eq 1;
  assert a*d+b*minus_c eq 1;
  c := -minus_c;
  assert a*d-b*c eq 1;
  // the other element is then c tau
  tau := c_a^(-1)*(c*B[1]+d*B[2]);
  assert c_a*ideal<Order(fraka) | [1,tau]> eq fraka;
  tau_CC := embed_quad(tau, CC);
  return CC!c_a, tau_CC;
end function;

// size of the torsion part of the unit group
function W(K)
  possible_cyc := &join{Set(EulerPhiInverse(m)) : m in Divisors(Degree(K))};
  K_cyc := 1;
  for c in possible_cyc do
    print "checking ", c, "...";
    if HasRoot(CyclotomicPolynomial(c), K) then
      K_cyc := LCM(K_cyc, c);
    end if;
  end for;
  return K_cyc;
end function;

function StarkUnitImaginaryQuadratic(K_over_F, M, prec)
  CC := ComplexField(prec);
  frakN := Conductor(AbelianExtension(K_over_F));
  rcgN, m_rcgN := RayClassGroup(frakN);
  // For our example, W(K) = 6, W(FN) = 42
  FN := AbsoluteField(NumberField(RayClassField(frakN)));
  w := W(K) / W(FN);
  s := 1;
  for rcg_elt in rcgN do
    a := m_rcgN(rcg_elt);
    c, tau := find_c_tau(a, CC);
    s *:= TruncatedSiegel(tau, c, M);
  end for;
  return s^w;
end function;

// This is Dedekind Eta function up to precision M
function Eta(z : M := 10)
  CC<i> := Parent(z);
  pi := Pi(CC);
  eta := Exp(2*pi*i*z/24);
  for m in [1..M] do
    eta *:= 1 - Exp(2*pi*i*m*z);
  end for;
  return eta;
end function;

// This is Theta1 as defined in Stark (9) p. 207
// This is an infinite product, so M is the 
// truncation bound
function Theta1(gamma, z : M := 10)
  CC<i> := Parent(z);
  assert CC eq Parent(gamma);
  pi := Pi(CC);
  ret := -i*Exp(pi*i*z/4)*(Exp(pi*i*gamma)-Exp(-pi*i*gamma));
  for m in [1..M] do
    ret *:= 1 - Exp(2*pi*i*(m*z+gamma));
    ret *:= 1 - Exp(2*pi*i*(m*z-gamma));
    ret *:= 1 - Exp(2*pi*i*m*z);
  end for;
  return ret;
end function;

// This is the function Phi as defined in Stark (10) p. 207
function TruncatedPhi(u, v, z : M := 10)
  CC<i> := Parent(z);
  assert CC eq Parent(u) and CC eq Parent(v);
  pi := Pi(CC);
  eta := DedekindEta(z);
  my_eta := Eta(z : M := M);
  assert Abs(my_eta - eta) lt 10^(-Precision(CC)/2);
  ret := Exp(pi*i*u*(u*z+v))*Theta1(u*z+v, z : M := M)/eta;
  return ret;
end function;

function F(r,s,z, N : M := 10)
  return TruncatedPhi(r/N, s/N, z)^(12*N);
end function;

// following Stark original paper p.223
// Here, fraka = fraka_0 is representing the
// ray class frakc
// and frakf is the conductor
function StarkE(fraka, frakf, CC)
  // Should this be norm or minimum? check
  frakb := Order(fraka)!!(Norm(fraka)*fraka^(-1));
  // Point of frakb is to be an integral ideal relatively prime to
  // frakf such that ab is principal.
  assert IsIntegral(frakb);
  assert IsCoprime(frakb,frakf);
  is_principal, alpha := IsPrincipal(fraka*frakb);
  assert is_principal;
  mu, nu := Explode(Basis(frakb*frakf));
  theta := mu/nu;
  mat_bf := Matrix(Rationals(), [Eltseq(bb) : bb in [mu,nu]]);
  sol := Solution(mat_bf, Vector(Rationals(),Eltseq(alpha)));
  u,v := Explode(Eltseq(sol));
  assert alpha eq u*mu + v*nu;
  f := Minimum(frakf);
  assert IsIntegral(f*u);
  assert IsIntegral(f*v);
  assert alpha/nu eq u*theta + v;
  ret := TruncatedPhi(CC!u,CC!v,embed_quad(theta, CC))^(12*f);
  _<i> := CC;
  pi := Pi(CC);
  // testing modularity properties
  assert TruncatedPhi(CC!u,CC!v+1,embed_quad(theta, CC)) eq -Exp(pi*i*u)*ret;
  assert TruncatedPhi(CC!u+1,CC!v+1,embed_quad(theta, CC)) eq -Exp(-pi*i*v)*ret;
  return ret;
end function;



function StarkOriginalE(K_over_F, M, prec)
  CC := ComplexField(prec);
  frakf := Conductor(AbelianExtension(K_over_F));
  rcgf, m_rcgf := RayClassGroup(frakf);
  frakc := rcgf.1;
  fraka := m_rcgf(frakc);
  return 0;
end function;

function Theta(t, alpha, beta, CC : M := 10)
  assert t gt 0;
  _<i> := CC;
  pi := Pi(CC);
  s := 0;
  for m in [-M..M] do
    s +:= Exp(-pi*t*(n + alpha)^2 + 2*pi*i*n*beta);
  end for;
  return s;
end function;

procedure testTheta(t, alpha, beta, prec, M)
  C<i> := ComplexField(prec);
  pi := Pi(CC);
  // transformation formula
  theta := Theta(t,alpha, beta, CC : M := M);
  trtheta := Exp(-2*pi*i*alpha*beta)*1/Sqrt(CC!t)*Theta(t^(-1),-beta, alpha, CC : M := M);
  eps := 10^(-1);
  assert Abs(theta - trtheta) lt eps;
end procedure;

procedure testTheta1(gamma, z, prec, M)
  C<i> := ComplexField(prec);
  theta := Theta(-i*z, CC!1/2, gamma - 1/2, CC : M := M);
  theta1 := Theta1(gamma, z : M := M);
  eps := 1; // ? This should depend on the sizes of gamma and z
  // Jacobi triple product formula
  assert Abs(theta1 + i*Exp(pi*i*gamma)*theta) lt eps;
  // another check
  sm := &+[Exp(pi*i*z*(n+1/2)^2+2*pi*i*(n+1/2)*(gamma-1/2)) : n in [-M..M]];
  assert Abs(theta1 - sm) lt eps;
end procedure;

procedure testPhi(u, v, z, CC, M)
  _<i> := CC;
  pi := Pi(CC);
  phi := TruncatedPhi(CC!u,CC!v,z+1);
  tr_phi := TruncatedPhi(CC!u,CC!u+v,z)*Exp(pi*i/6);
  eps := 10^(-Precision(CC)/2);
  assert Abs(phi - tr_phi) lt eps;
  phi := TruncatedPhi(CC!u,CC!v,-1/z : M := M*Floor(Im(z)));
  tr_phi := TruncatedPhi(CC!v,-CC!u,z)*Exp(-pi*i/2);
  assert Abs(phi - tr_phi) lt eps;
  phi := TruncatedPhi(-CC!u, -CC!v, z);
  tr_phi := -TruncatedPhi(CC!u, CC!v, z);
  assert Abs(phi - tr_phi) lt eps;
end procedure;

// Needs to handle the case where the primitive character is trivial.
function lfunc(chi, prec)
  //chi0 := AssociatedPrimitiveCharacter(chi);
  //Lchi0 := LSeries(chi0 : Precision := prec);
  m := Modulus(chi);
  //f := Modulus(chi0);
  F := NumberField(Order(Modulus(chi)));
  function local_factor(p, d : Precision := 0)
    _<T> := PolynomialRing(Integers());
    return &*[1 - chi(pp)*T^Degree(ResidueClassField(pp)) : pp in PrimeIdealsOverPrime(F,p)];
  end function;
  cond := -Discriminant(F) * Norm(m);
  Lchi := LSeries(1, [0,1], cond, local_factor : Sign := chi(-1), Poles := [1], Precision := prec);
  /*
  for pe in Factorization(m div (m+f)) do
    P := pe[1];
    p := Minimum(P);
    euler := &*[EulerFactor(Lchi0, pp) div (1 - chi0(pp)*T) : pp in PrimeIdealsOverPrime(F,p)];
    Lchi := ChangeEulerFactor(Lchi0, p, euler);
  end for;
  */
end function;

// test for an abelian extension of an imaginary quadratic
function testStarkUnit(K : prec := Precision(GetDefaultRealField()))
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
  eps := 10^(-5);
  for chi in Elements(X) do
    unit_eqn := -1/(6*f*w_frakf) * &+[chi(m_rcgf(c))*Log(AbsoluteValue(StarkE(m_rcgf(c),frakf,CC))) : c in rcgf];
    chi0 := AssociatedPrimitiveCharacter(chi);
    Lchi := LSeries(chi : Precision := prec);
    Lvalue := Evaluate(Lchi, 0 : Derivative := 1);
    assert Abs(Lvalue - unit_eqn) lt eps;
  end for;
end function;