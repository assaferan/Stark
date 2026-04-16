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

function SiegelPhi(u, v, z)
  CC<i> := Parent(z);
  assert CC eq Parent(u) and CC eq Parent(v);
  pi := Pi(CC);
  eta := DedekindEta(z);
  gamma := u*z + v;
  // We use transformation properties to make it more accurate
  // Otherwise we get Infs for large values of u and v
  // !! TODO - add the general version to Magma's implementation
  n_v := Floor(v);
  if n_v ne 0 then
    return (-1)^n_v*Exp(pi*i*u*n_v)*SiegelPhi(u, v - n_v, z);
  end if;
  n_u := Floor(u);
  if n_u ne 0 then
    return (-1)^n_u*Exp(pi*i*v*n_u)*SiegelPhi(u - n_u, v, z);
  end if;
  // Now both u and v are in [0,1)
  // Q : Should we also bring z to the fundamental domain?
  theta1 := Theta(Matrix([[1/2],[-1/2]]), Matrix([[gamma]]), Matrix([[z]]));
  ret := Exp(pi*i*u*gamma)*theta1/eta;
  return ret;
end function;

// Here F_{r,s}(z) \in M_0(Gamma(N))
// is the function Stark constructs in p. 209
function StarkF(r, s, z, N)
  CC := Parent(z);
  return SiegelPhi(CC!r/N, CC!s/N, z)^(12*N);
end function;

function embed_quad(tau, CC : Sign := 1)
  t := CC!Trace(tau);
  n := CC!Norm(tau);
  tau_CC := 1/2*(t+Sqrt(t^2 - 4*n));
  if Im(tau_CC)*Sign lt 0 then
    tau_CC := ComplexConjugate(tau_CC);
  end if;
  return tau_CC;
end function;

// following Stark original paper p.223
// Here, fraka = fraka_0 is representing the
// ray class frakc
// and frakf is the conductor
// At the moment only works for the Ray class field
function StarkERCF(fraka, frakf, CC)
  O := Order(fraka);
  F := NumberField(O);
  // Should this be norm or minimum? check
  frakb := O!!(Norm(fraka)*fraka^(-1));
  // Point of frakb is to be an integral ideal relatively prime to
  // frakf such that ab is principal.
  assert IsIntegral(frakb);
  assert IsCoprime(frakb,frakf);
  is_principal, alpha := IsPrincipal(fraka*frakb);
  assert is_principal;
  mu, nu := Explode(Basis(frakb*frakf));
  theta := (F!mu)/(F!nu);
  mat_bf := Matrix(Rationals(), [Eltseq(bb) : bb in [mu,nu]]);
  sol := Solution(mat_bf, Vector(Rationals(),Eltseq(alpha)));
  u,v := Explode(Eltseq(sol));
  assert alpha eq u*mu + v*nu;
  f := Minimum(frakf);
  assert IsIntegral(f*u);
  assert IsIntegral(f*v);
  assert alpha/nu eq u*theta + v;
  // we want theta, u theta  + v in H
  // so u must be positive
  // replacing mu by -mu, leads to replacing u by -u
  // and theta by -theta
  if u lt 0 then
    u := -u;
    theta := -theta;
  end if;
  theta_CC := embed_quad(theta, CC);
  // ret := TruncatedPhiNew(CC!u,CC!v,theta_CC)^(12*f);
  ret := StarkF(f*u, f*v, theta_CC, f);
  //_<i> := CC;
  //pi := Pi(CC);
  // testing modularity properties
  // assert TruncatedPhi(CC!u,CC!v+1,embed_quad(theta, CC)) eq -Exp(pi*i*u)*ret;
  // assert TruncatedPhi(CC!u+1,CC!v+1,embed_quad(theta, CC)) eq -Exp(-pi*i*v)*ret;
  return ret;
end function;

// This is E(c') for an arbitrary abelian extension
function StarkE(frakc_prime, frakf, CC, J)
  return &*[StarkERCF(frakc_prime*j, frakf, CC) : j in J];
end function;

// computes all the E(c) from [Stark, Lemma 7]
function AllStarks(K : prec := Precision(GetDefaultRealField()))
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
  starks := [StarkE(m_rcgf(c),frakf,CC, J_idls) : c in coset_reps];
  return starks;
end function;