
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
function TruncatedSiegel(CC, tau, z, M)
  _<i> := CC;
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
  return TruncatedSiegel(CC, tau, z, M);
end function;

// computing the c_{a,b} from A.4
// !!! TODO - verify that this is the correct Stickelberger element
function StickelbergerCoefficient(a,b)
  nm := a^2 + a*b + b^2;
  c := nm mod 7;
  return 21 - 6*c;
end function;

// Construct the unit \prod Siegel(a,b)^{c_{a,b}}
function ConstructUnit(CC, M)
  return &*[SiegelAt7Torsion(CC,a,b,M)^StickelbergerCoefficient(a,b)
	       : a, b in [0..6] | a + b gt 0];
end function;

function StarkUnit(M, prec : bd := 11035)
  f, beta := AlgebraicPolynomial();
  f_CC := AnalyticPolynomial(f, beta : prec := prec);
  CC<i> := BaseRing(f_CC);
  u := ConstructUnit(CC, M);
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
