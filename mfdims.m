freeze;

/*
    Dependencies: utils.m

    This module implements various intrinsics for efficiently computing Q-dimensions of spaces of modular forms.
    The TraceForm intrinsic shells out to Pari/GP and won't work if gp is not installed.
    
    Copyright (c) Andrew V. Sutherland, 2017-2025.  See License file for details on copying and usage.
*/

ZZ := Integers();
QQ := Rationals();

sum := func<a|#a eq 0 select 0 else &+a>;
prod := func<a|#a eq 0 select 0 else &*a>;
mu0 := func<n|ZZ!(n*&*[QQ|(p+1)/p: p in PrimeDivisors(n)])>;
mu20 := func<n|n mod 4 eq 0 select 0 else &*[ZZ|1+KroneckerSymbol(-4,p) : p in PrimeDivisors(n)]>;
mu30 := func<n|(n mod 2 eq 0 or n mod 9 eq 0) select 0 else &*[ZZ|1+KroneckerSymbol(-3,p) : p in PrimeDivisors(n)]>;
c0 := func<n|&+[EulerPhi(GCD(d,n div d)) : d in Divisors(n)]>;
g0 := func<n|1 + (mu0(n) - 3*mu20(n) - 4*mu30(n) - 6*c0(n)) div 12>;
mu1 := func<n|n le 2 select mu0(n) else (EulerPhi(n)*mu0(n)) div 2>;
mu21 := func<n|n le 2 select 1 else 0>;
mu31 := func<n|n eq 1 or n eq 3 select 1 else 0>;
c1 := func<n|n le 4 select [1,2,2,3][n] else &+[EulerPhi(d)*EulerPhi(n div d) div 2 : d in Divisors(n)]>;
g1 := func<n|1 + (mu1(n) - 3*mu21(n) - 4*mu31(n) - 6*c1(n)) div 12>;
S0 := func<n,k|k eq 2 select g0(n) else (k-1)*(g0(n)-1) + (k div 2 - 1)*c0(n)+mu20(n)*Floor(k/4)+mu30(n)*Floor(k/3)>; // assumes k > 0 is even
S1 := func<n,k|k eq 2 select g1(n) else (n lt 3 select S0(n,k) else (k-1)*(g1(n)-1) + ZZ!((k/2 - 1)*c1(n) + (n eq 4 and IsOdd(k) select 1/2 else (n eq 3 select k div 3 else 0))))>;
idxG0 := func<n|&*[ZZ|a[1]^a[2] + a[1]^(a[2]-1) : a in Factorization(n)]>;
idxG1 := func<n|EulerPhi(n)*idxG0(n)>;

// Function defined on page 72 of https://doi.org/10.1007/BFb0065297 (Cohen-Oesterle article Dimensions des espaces de formes modulaires in Modular Functions of One Variable VI)
lambda := func<r,s,p|2*s gt r select 2*p^(r-s) else (2*x eq r select p^x + p^(x-1) else 2*p^x where x := r div 2)>;

// Formula worked out by Kevin Buzzard in http://wwwf.imperial.ac.uk/~buzzard/maths/research/notes/dimension_of_spaces_of_eisenstein_series.pdf, with one ovious typo corrected (2*s==r, p>2 case)
new_lambda := func<r,s,p|2*s gt r select (r eq s select 2 else (r eq s+1 select 2*p-4 else 2*(p-1)^2*p^(r-s-2)))
                                  else (2*s eq r select (p eq 2 select 0 else (s eq 1 select p-3 else (p-2)*(p-1)*p^(s-2)))
                                   else (IsOdd(r) select 0
                                    else (r eq 2 select p-2
                                     else (p-1)^2*p^(r div 2 - 2))))>;

z4modp := func<p|ZZ!Roots(x^2+1)[1][1] where x:=PolynomialRing(GF(p)).1>;
z3modp := func<p|ZZ!Roots(x^2+x+1)[1][1] where x:=PolynomialRing(GF(p)).1>;

CO_delta := func<r,p,N,n|p mod 4 eq 3 select 0 else (p eq 2 select (r eq 1 select 1 else 0) else (a eq 1 select 2 else (a eq 1/2 select -2 else 0) where a:= ConreyCharacterAngle(N,n,ZZ!(Integers(N)!CRT([z4modp(p),1],[p, N div p^r]))^(p^(r-1)))))>;
CO_nu := func<r,p,N,n|p mod 3 eq 2 select 0 else (p eq 3 select (r eq 1 select 1 else 0) else (a eq 1 select 2 else -1 where a:= ConreyCharacterAngle(N,n,ZZ!(Integers(N)!CRT([z3modp(p),1],[p, N div p^r]))^(p^(r-1)))))>;

mumu := func<N|&*[ZZ|a[2] gt 2 select 0 else (a[2] eq 1 select -2 else 1):a in Factorization(N)]>;

function CO (N,n,k)
    fN := Factorization(N); fC := [<a[1],Valuation(Conductor(N,n),a[1])> : a in fN];
    gamma_k := IsOdd(k) select 0 else (k mod 4 eq 2 select -1/4 else 1/4);
    mu_k := kmod3 eq 1 select 0 else (kmod3 eq 2 select -1/3 else 1/3) where kmod3 := k mod 3;
    return -(1/2) * &*[lambda(fN[i][2],fC[i][2],fN[i][1]) : i in [1..#fN]] + gamma_k * &*[CO_delta(a[2],a[1],N,n) : a in fN] + mu_k * &*[CO_nu(a[2],a[1],N,n) : a in fN];
end function;

intrinsic QDimension (S::ModSym) -> RngIntElt
{ Q-dimension of the space of modular symbols S. }
    return Dimension(S)*Degree(DirichletCharacter(S));
end intrinsic;

intrinsic QDimensionModularForms (chi::GrpDrchElt,k::RngIntElt) -> RngIntElt
{ Q-dimension of the space M_k(N,chi) of weight-k modular forms for Gamma0(N) with character chi (where N is the modulus of chi). }
    return Dimension(ModularSymbols(chi,k,-1))*Degree(chi);
end intrinsic;

intrinsic QDimensionModularForms (N::RngIntElt,k::RngIntElt) -> RngIntElt
{ Q-dimension of the space M_k(N) of weight-k modular forms from Gamma0(N). }
    return Dimension(ModularSymbols(N,k,-1));
end intrinsic;

intrinsic QDimensionModularFormsGamma1 (N::RngIntElt,k::RngIntElt) -> RngIntElt
{ Q-dimension of the space of weight-k modular forms for Gamma1(N). }
    require N gt 0 and k gt 1: "N must be a positive integer and k must be greater than 1";
    if N eq 1 then return IsEven(k) select k div 12 + (k mod 12 eq 2 select 0 else 1) else 0;
    elif N eq 2 then return IsEven(k) select 3*k div 12 + 1 else 0;
    elif N eq 3 then return 4*k div 12 + 1;
    elif N eq 4 then return 6*k div 12 + 1;
    else
        s := func<A|&*[ZZ|a[1]^(2*a[2]-2)*(a[1]^2-1):a in A]>;
        u := func<A|&*[ZZ|a[1]^(a[2]-2)*(a[1]^2-1+a[2]*(a[1]-1)^2):a in A]>;
        return ExactQuotient((k-1)*s(A)+6*u(A),24) where A:=Factorization(N);
    end if;
end intrinsic;

// See Proposition 15 in https://arxiv.org/pdf/math/0306128
intrinsic QDimensionCuspFormsGamma1 (N::RngIntElt,k::RngIntElt) -> RngIntElt
{ Q-dimension of the space of weight-k cusp forms for Gamma1(N). }
    require N gt 0 and k gt 1: "N must be a positive integer and k must be greater than 1";
    if N eq 1 then return IsEven(k) select k div 12 - (k mod 12 eq 2 and k ne 2 select 1 else 0) else 0;
    elif N eq 2 then return IsEven(k) select 3*k div 12 - (k eq 2 select 0 else 1) else 0;
    elif N eq 3 then return 4*k div 12 - (k eq 2 select 0 else 1);
    elif N eq 4 then return 6*k div 12 - (IsEven(k) and k ne 2 select 2 else 1);
    else
        s := func<A|&*[ZZ|a[1]^(2*a[2]-2)*(a[1]^2-1):a in A]>;
        u := func<A|&*[ZZ|a[1]^(a[2]-2)*(a[1]^2-1+a[2]*(a[1]-1)^2):a in A]>;
        return ExactQuotient((k-1)*s(A) - 6*u(A), 24) + (k eq 2 select 1 else 0) where A:=Factorization(N);
    end if;
end intrinsic;

intrinsic QDimensionEisensteinFormsGamma1 (N::RngIntElt,k::RngIntElt) -> RngIntElt
{ Q-dimension of the space of weight-k Eisenstein forms for Gamma1(N). }
    return QDimensionModularFormsGamma1(N,k) - QDimensionCuspFormsGamma1(N,k);
end intrinsic;

// lambda := func<N|&*[QQ|a[2] eq 1 select -2 else (a[2] eq 2 select 1 else 0):a in A] where A:=Factorization(N)>;

// See Proposition 13 in https://arxiv.org/pdf/math/0306128
intrinsic QDimensionNewCuspFormsGamma1 (N::RngIntElt,k::RngIntElt) -> RngIntElt
{ Q-dimension of the space of new cusp forms of weight k for Gamma1(N). }
    require N gt 0 and k gt 1: "N must be a positive integer and k must be greater than 1";
    A := Factorization(N); mu := k eq 2 and &and[a[2] lt 2:a in A] select (-1)^#A else 0;
    b1 := func<k|(IsEven(k) select k+A[1+((k div 2) mod 6)] else 7-k) where A:=[7,-21,-1,-5,-9,-13]>;
    b2 := func<k|IsEven(k) select 3*k-(k mod 4 eq 2 select 21 else 9) else 15-3*k>;
    b3 := func<k|8*(1-(k mod 3))>;
    b4 := func<k|IsEven(k) select -6 else 6>;
    splus := &*[ZZ|(a[2] eq 1 select a[1]^(2*a[2]-2)*(a[1]^2-3) else (a[2] eq 2 select a[1]^(2*a[2]-4)*(a[1]^4-3*a[1]^2+3) else a[1]^(2*a[2]-6)*(a[1]^2-1)^3)):a in A];
    uplus := &*[ZZ|a[2] eq 1 select 2*a[1]-4 else (a[2] eq 2 select 3*a[1]^2-8*a[1]+6 else a[1]^(a[2]-4)*(a[1]-1)^3*((a[2]+1)*a[1]-a[2]+3)):a in A];
    l1 := &*[ZZ|a[2] eq 1 select -2 else (a[2] eq 2 select 1 else 0):a in A|a[1] gt 3]; l2 := 0; l3 := 0; l4 := 0;
    v2 := Valuation(N,2);
    if v2 eq 1 then l2:=l1; l1*:=-2; elif v2 eq 2 then l2:=-2*l1; l4:=l1; elif v2 eq 3 then l2:=l1; l4:=-2*l1; l1:=0; elif v2 eq 4 then l4:=l1; l1:=0; elif v2 gt 4 then l1:=0; end if;
    v3 := Valuation(N,3);
    if v3 eq 1 then l3:=l1; l1*:=-2; l2*:=-2; l4*:=-2; elif v3 eq 2 then l3:=-2*l1; elif v3 eq 3 then l3:=l1; l1:=0; l2:=0; l4:=0; elif v3 gt 3 then l1:=0; l2:=0; l4:=0; end if; 
    return ExactQuotient((k-1)*splus - 6*uplus + b1(k)*l1 + b2(k)*l2 + b3(k)*l3 + b4(k)*l4, 24) + mu;
end intrinsic;

intrinsic QDimensionOldCuspFormsGamma1 (N::RngIntElt,k::RngIntElt) -> RngIntElt
{ Q-dimension of the space of old cusp forms of weight k for Gamma1(N). }
    return QDimensionCuspFormsGamma1(N,k) - QDimensionNewCuspFormsGamma1(N,k);
end intrinsic;

intrinsic DimensionCuspForms(N::RngIntElt,n::RngIntElt,k::RngIntElt) -> RngIntElt
{ Dimension of the space S_k(N,chi), where chi is the Dirichlet character with Conrey label N.n as a vector space over the charater field. }
    require k ge 2: "Weight k must be at least 2.";
    if N eq 1 or n eq 1 then return IsEven(k) select S0(N,k) else 0; end if;
    if Parity(N,n) ne (-1)^k then return 0; end if;
    return Integers()!(idxG0(N) * (k-1)/12 + CO(N,n,k));
end intrinsic;

intrinsic QDimensionCuspForms (N::RngIntElt,n::RngIntElt,k::RngIntElt) -> RngIntElt
{ Q-dimension of the space S_k(N,chi) where chi is the Dirichlet character with Conrey label N.n. }
    return DimensionCuspForms(N,n,k)*Degree(N,n);
end intrinsic;

intrinsic QDimensionCuspForms (chi::GrpDrchElt,k::RngIntElt) -> RngIntElt
{ The Q-dimension of the space S_k(N,chi) of cuspidal modular forms of weight k, level N, and character chi, where N is the modulus of chi. }
    if k eq 1 then return Dimension(ModularForms(chi,k)); end if;
    return DimensionCuspForms(chi,k)*Degree(chi);
end intrinsic;

intrinsic QDimensionCuspForms (s::MonStgElt,k::RngIntElt) -> RngIntElt
{ The Q-dimension of the space S_k(N,chi) of cuspidal modular forms of weight k, level N, and character chi, where N is the modulus of chi. }
    N,n := ConreyCharacterFromLabel(s);
    return QDimensionCuspForms(N,n,k);
end intrinsic;

intrinsic DimensionNewCuspForms(N::RngIntElt,n::RngIntElt,k::RngIntElt) -> RngIntElt
{ Dimension of the new part of S_k(N,chi), where chi is the Dirichlet character with Conrey label N.n as a vector space over the charater field. }
    require k ge 2: "Weight k must be at least 2.";
    C := Conductor(N,n);
    return &+[DimensionCuspForms(M,AssociatedCharacter(M,N,n),k)*mumu(N div M) where M:=C*d : d in Divisors(N div C)];
end intrinsic;

intrinsic QDimensionNewCuspForms (N::RngIntElt,n::RngIntElt,k::RngIntElt) -> RngIntElt
{ Q-dimension of the space S_k(N,chi) where chi is the Dirichlet character with Conrey label N.n. }
    return DimensionNewCuspForms(N,n,k)*Degree(N,n);
end intrinsic;

intrinsic QDimensionNewCuspForms (chi::GrpDrchElt,k::RngIntElt) -> RngIntElt
{ The Q-dimension of the new subspace of cuspdial forms of weight k, level N, and character chi, where N is the modulus of chi. }
    // This is very slow in weight 1, but it works
    return k eq 1 select  QDimensionCuspForms(chi,k) - QDimensionOldCuspForms(chi,k) else DimensionNewCuspForms(chi,k)*Degree(chi);
end intrinsic;
    
intrinsic QDimensionNewCuspForms (s::MonStgElt,k::RngIntElt) -> RngIntElt
{ The Q-dimension of the new subspace of cuspdial forms of weight k, level N, and character chi, where N is the modulus of chi. }
    N,n := ConreyCharacterFromLabel(s);
    return QDimensionNewCuspForms(N,n,k);
end intrinsic;
    
intrinsic QDimensionNewCuspForms (s::MonStgElt) -> RngIntElt
{ The Q-dimension of the new subspace of cuspdial forms of weight k, level N, and character chi, where N is the modulus of chi. }
    t := Split(s,".");
    require #t eq 3: "Invalid newspace label";
    N,n := ConreyCharacterFromLabel(t[1] cat "." cat t[3]);
    return QDimensionNewCuspForms(N,n,atoi(t[2]));
end intrinsic;

intrinsic QDimensionOldCuspForms (N::RngIntElt,n::RngIntElt,k::RngIntElt) -> RngIntElt
{ The Q-dimension of the old subspace S_k(N,chi) of cuspidal modular forms of weight k, level N, and character chi, where N is the modulus of chi. }
    P,p := AssociatedPrimitiveCharacter(N,n);
    d := ExactQuotient(N,P);
    return sum([QDimensionNewCuspForms(M,AssociatedCharacter(M,P,p),k)*#Divisors(ExactQuotient(N,M)) where M := P*m : m in Divisors(d) | m ne d]);
end intrinsic;

intrinsic QDimensionOldCuspForms (chi::GrpDrchElt,k::RngIntElt) -> RngIntElt
{ The Q-dimension of the old subspace S_k(N,chi) of cuspidal modular forms of weight k, level N, and character chi, where N is the modulus of chi. }
    N := Modulus(chi);
    psi := AssociatedPrimitiveCharacter(chi);
    c := Modulus(psi);  d := ExactQuotient(N,c);
    return sum([QDimensionNewCuspForms(FullDirichletGroup(M)!psi,k)*#Divisors(ExactQuotient(N,M)) where M := c*n : n in Divisors(d) | n ne d]);
end intrinsic;

intrinsic QDimensionOldCuspForms (s::MonStgElt,k::RngIntElt) -> RngIntElt
{ The Q-dimension of the old subspace S_k(N) of cuspidal modular forms of weight k, level N, and character chi, where N is the modulus of chi. }
    return QDimensionOldCuspForms(DirichletCharacter(s),k);
end intrinsic;

intrinsic QDimensionOldCuspForms (N::RngIntElt,k::RngIntElt) -> RngIntElt
{ The Q-dimension of the old subspace of cuspdial forms of weight k for Gamma0(N). }
    return QDimensionOldCuspForms(DirichletGroup(N)!1,k);
end intrinsic;

intrinsic QDimensionEisensteinForms (chi::GrpDrchElt,k::RngIntElt) -> RngIntElt
{ The Q-dimension of the space E_k(N,chi) of Eisenstein series of weight k, level N, and character chi, where N is the modulus of chi. }
    require k gt 0: "The weight k must be a positive integer";
    if IsOdd(k) ne IsOdd(chi) then return 0; end if;
    N := Modulus(chi);  M := Conductor(chi);
    if N eq 1 then return k gt 2 select 1 else 0; end if;
    D := prod([lambda(Valuation(N,p),Valuation(M,p),p):p in PrimeDivisors(N)]);
    if k eq 2 and Order(chi) eq 1 then D -:= 1; end if;
    // As noted by Buzzard, to handle the weight 1 case, one simply divides by 2
    if k eq 1 then D := ExactQuotient(D,2); end if;
    return D*Degree(chi);
end intrinsic;

intrinsic QDimensionEisensteinForms (N::RngIntElt,n::RngIntElt,k::RngIntElt) -> RngIntElt
{ The Q-dimension of the space E_k(N,chi) of Eisenstein series of weight k, level N, and character chi, where chi is the Dirichlet character with label N.n. }
    require k gt 0: "The weight k must be a positive integer";
    if (-1)^k ne Parity(N,n) then return 0; end if;
    M := Conductor(N,n);
    if N eq 1 then return k gt 2 select 1 else 0; end if;
    D := prod([lambda(Valuation(N,p),Valuation(M,p),p):p in PrimeDivisors(N)]);
    if k eq 2 and Order(Integers(N)!n) eq 1 then D -:= 1; end if;
    // As noted by Buzzard, to handle the weight 1 case, one simply divides by 2
    if k eq 1 then D := ExactQuotient(D,2); end if;
    return D*Degree(N,n);
end intrinsic;

intrinsic QDimensionEisensteinForms (s::MonStgElt,k::RngIntElt) -> RngIntElt
{ The Q-dimension of the space E_k(N,chi) of Eisenstein series of weight k, level N, and character chi with label s. }
    N,n := ConreyCharacterFromLabel(s);
    return QDimensionEisensteinForms (N,n,k);
end intrinsic;

intrinsic QDimensionEisensteinForms (N::RngIntElt,k::RngIntElt) -> RngIntElt
{ The Q-dimension of the space E_k(N,chi) of Eisenstein series of weight k for Gamma0(N). }
    return QDimensionEisensteinForms (N,1,k);
end intrinsic;

intrinsic QDimensionNewEisensteinForms (chi::GrpDrchElt,k::RngIntElt) -> RngIntElt
{ The Q-dimension of the new subspace of E_k(N,chi), the space of Eisenstein series of weight k, level N, and character chi, where N is the modulus of chi. }
    require k gt 0: "The weight k must be a positive integer";
    if IsOdd(k) ne IsOdd(chi) then return 0,0; end if;
    N := Modulus(chi);  M := Conductor(chi);
    if N eq 1 then return k gt 2 select 1 else 0; end if;
    D := prod([new_lambda(Valuation(N,p),Valuation(M,p),p):p in PrimeDivisors(N)]);
    if k eq 2 and Order(chi) eq 1 and IsPrime(N) then D +:= 1; end if;
    // As noted by Buzzard, to handle the weight 1 case, one simply divides by 2
    if k eq 1 then D := ExactQuotient(D,2); end if;
    return D*Degree(chi);
end intrinsic;

intrinsic QDimensionNewEisensteinForms (N::RngIntElt,n::RngIntElt,k::RngIntElt) -> RngIntElt
{ The Q-dimension of the new subspace of E_k(N,chi), the space of Eisenstein series of weight k, level N, and character chi, where chi is the Dirichlet character with Conrey label N.n. }
    require k gt 0: "The weight k must be a positive integer";
    if (-1)^k ne Parity(N,n) then return 0; end if;
    M := Conductor(N,n);
    if N eq 1 then return k gt 2 select 1 else 0; end if;
    D := prod([new_lambda(Valuation(N,p),Valuation(M,p),p):p in PrimeDivisors(N)]);
    if k eq 2 and Order(Integers(N)!n) eq 1 and IsPrime(N) then D +:= 1; end if;
    // As noted by Buzzard, to handle the weight 1 case, one simply divides by 2
    if k eq 1 then D := ExactQuotient(D,2); end if;
    return D*Degree(N,n);
end intrinsic;

intrinsic QDimensionNewEisensteinForms (s::MonStgElt,k::RngIntElt) -> RngIntElt
{ The Q-dimension of the new subspace of E_k(N,chi), the space of Eisenstein series of weight k, level N, and character chi with label s. }
    N,n := ConreyCharacterFromLabel(s);
    return QDimensionNewEisensteinForms (N,n,k);
end intrinsic;

intrinsic QDimensionNewEisensteinForms (N::RngIntElt,k::RngIntElt) -> RngIntElt
{ The Q-dimension of the space E_k(N,chi) of Eisenstein series of weight k for Gamma0(N). }
    return QDimensionNewEisensteinForms (N,1,k);
end intrinsic;

intrinsic NumberOfGamma1CuspSpaces (B::RngIntElt) -> RngIntElt
{ The number of spaces S_k(N,chi) with N*k^2 <= B (includes spaces that are empty because parity(k) != parity(chi). }
    return &+[NumberOfCharacterOrbits(N)*Floor(Sqrt(B/N)):N in [1..B]];
end intrinsic;

intrinsic NumberOfGamma0CuspSpaces (B::RngIntElt) -> RngIntElt
{ The number of spaces S_k(N,chi) with N*k^2 <= B (includes spaces that are empty because parity(k) != parity(chi)). }
    return &+[Floor(Sqrt(B/N)):N in [1..B]];
end intrinsic;

intrinsic NumberOfNewspaces (B::RngIntElt:MaxN:=0,Maxk:=0,SkipWeightOne:=false,TrivialCharOnly:=false) -> RngIntElt
{ Number of newspaces S_k^new(N,chi) with Nk^2 <= B (and satisfying optional restrictions on N, k, and char). }
    if MaxN eq 0 then MaxN := SkipWeightOne select B div 4 else B; end if;
    if Maxk eq 0 then Maxk := Floor(Sqrt(B)); end if;
    k0 := SkipWeightOne select 1 else 0;
    if TrivialCharOnly then return &+[Min(Floor(Sqrt(B/N)),Maxk)-k0:N in [1..MaxN]]; end if;
    return &+[(Min(Floor(Sqrt(B/N)),Maxk)-k0) * NumberOfCharacterOrbits(N) : N in [1..MaxN]];
end intrinsic;


declare attributes RngInt: H12Cache, h6Cache;
ZZ := Integers(); QQ := Rationals(); RQQ<x> := PolynomialRing(QQ);
ZZ`H12Cache := AssociativeArray();
function H12(N)
    ZZ := Integers();
    if N le 0 then return ZZ!(12*HurwitzClassNumber(N)); end if;
    if not IsDefined(ZZ`H12Cache,N) then ZZ`H12Cache[N] := ZZ!(12*HurwitzClassNumber(N)); end if;
    return ZZ`H12Cache[N];
end function;

ZZ`h6Cache := AssociativeArray();
function h6(D)
    assert D lt 0 and D mod 4 in [0,1];
    ZZ := Integers();
    if not IsDefined(ZZ`h6Cache,-D) then ZZ`h6Cache[-D] := (6 div w)*ClassNumber(D) where  w := D lt -4 select 1 else (D lt -3 select 2 else 3); end if;
    return ZZ`h6Cache[-D];
end function;


// Popa18 formulas from https://link.springer.com/article/10.1007/s40687-018-0125-5 (with a bug fix for p=2)

function SNp(p,vN,vu,t,n) // p an odd prime, N = p^vN, u = p^vu, assumes vN > 0
    D := t^2-4*n; s := KroneckerSymbol(D,p);
    if s lt 0 then return 0; end if;
    if s gt 0 then return n mod p eq 0 select 1 else 2; end if;
    if n mod p eq 0 or t mod p eq 0 then return 0; end if;
    if vu eq vN then return 1; end if;
    if D eq 0 then return p^((vN-vu) div 2); end if; 
    vD := Valuation(D,p);
    if vD ge vN+vu then return p^((vN-vu) div 2); end if;
    if vD mod 2 eq 1 or KroneckerSymbol(D div p^vD,p) ne 1 then return 0; end if;
    return 2*p^(vD div 2 - vu);
end function;

function SNpbase(p,vN,t,n) // p an odd prime, N = p^vN, u = 1 assumes vN > 0A:
    D := t^2-4*n; s := KroneckerSymbol(D,p);
    if s lt 0 then return 0; end if;
    if s gt 0 then return n mod p eq 0 select 1 else 2; end if;
    if n mod p eq 0 or t mod p eq 0 then return 0; end if;
    if D eq 0 then return p^(vN div 2); end if; 
    vD := Valuation(D,p);
    if vD ge vN then return p^(vN div 2); end if;
    if vD mod 2 eq 1 or KroneckerSymbol(D div p^vD,p) ne 1 then return 0; end if;
    return 2*p^(vD div 2);
end function;

function SN2(vN,vu,t,n) // N = 2^vN, u=2^vu, assumes vN > 0
    D := t^2-4*n; s := KroneckerSymbol(D,2);
    if s lt 0 then return 0; end if;
    if s gt 0 then return n mod 2 eq 0 select 1 else 2; end if;
    if n mod 2 eq 0 then return 0; end if;
    if vu eq 0 and vN eq 1 then return 1; end if;
    if (t+n) mod 4 eq 1 then return 0; end if;
    if D eq 0 then return 2^((vN-vu) div 2); end if; 
    vD := Valuation(D,2);
    if vD ge vN+vu+2 then return 2^((vN-vu) div 2); end if;
    if vD mod 2 eq 1 then return 0; end if;
    d := (D div 2^vD) mod 8;
    return vD ge vN+vu+(d in [3,7] select 1 else 0) select 2^((vN-vu) div 2) else (d eq 1 select 2^(vD div 2 - vu+1) else 0);
end function;

function SN2base(vN,t,n) // N = 2^vN, u=1, assumes vN > 0
    D := t^2-4*n; s := KroneckerSymbol(D,2);
    if s lt 0 then return 0; end if;
    if s gt 0 then return 1 + n mod 2; end if;
    if n mod 2 eq 0 then return 0; end if;
    if vN eq 1 then return 1; end if;
    if (t+n) mod 4 eq 1 then return 0; end if;
    if D eq 0 then return 2^(vN div 2); end if; 
    vD := Valuation(D,2);
    if vD ge vN+2 then return 2^(vN div 2); end if;
    if vD mod 2 eq 1 then return 0; end if;
    d := (D div 2^vD) mod 8;
    return vD ge vN+(d in [3,7] select 1 else 0) select 2^(vN div 2) else (d eq 1 select 2^(vD div 2 + 1) else 0);
end function;

SNfast := func<N,u,t,n|&*[ZZ|a[1] eq 2 select SN2(vN,vu,t,n) else SNp(a[1],vN,vu,t,n) where vN:=a[2] where vu:=Valuation(u,a[1]):a in Factorization(N)]>;

Phi1 := func<N|&*[ZZ|a[1]^(a[2]-1)*(a[1]+1):a in Factorization(N)]>;
SNraw := func<N,u,t,n|#[a:a in [1..N]|GCD(a,N) eq 1 and (a^2-t*a+n) mod (N*u) eq 0]>;
BNraw := func<N,u,t,n|ExactQuotient(Phi1(N)*SNraw(N,u,t,n),Phi1(ExactQuotient(N,u)))>;
CNraw := func<N,u,t,n|&+[ZZ|BNraw(N,u div d,t,n)*MoebiusMu(d):d in Divisors(u)]>;

function CNp(p,vN,vu,t,n) // See Popa Lemma 4.5
    if vu eq 0 then return 1; end if;
    e := Ceiling(vu/2);
    if vu eq vN then return p^e; end if;
    m := (vN-vu) mod 2 eq 0;
    D := t^2-4*n;
    if D eq 0 then return (vu gt 0 and m) select (p^e-p^(e-1)) else 0; end if;
    vD := Valuation(D,p); v := vD-vN;
    if m then
        if vu le v then return (p^e-p^(e-1));
        elif vu eq v+1 then return (-p^(e-1));
        else return 0; end if;
    end if;
    return vu eq v+1 select (p^(vu div 2)*KroneckerSymbol(D div p^vD,p)) else 0;
end function;

function CN2(vN,vu,t,n) // Modification of Popa Lemma 4.5 to correct an error in thc case p=2, vN=vu (a=i in the paper's notation)
    if vu eq 0 then return 1; end if;
    e := Ceiling(vu/2); m := (vN-vu) mod 2 eq 0;
//    if vu eq vN then return 2^e; end if;
    D := t^2-4*n; vD := Valuation(D,2); v := vD-vN; r := D eq 0 select 0 else (D div 2^vD) mod 8;
    if m then
        if vu le v-2 then return vN eq vu select 2^e else 2^(e-1);
        elif vu eq v-1 then return -2^(e-1);
        elif vu eq v then return vu eq vN and r mod 4 eq 1 select 2^e else (2^(e-1)*(r mod 4 eq 1 select 1 else -1));
        else return 0; end if;
    end if;
    return vu eq v+1 and r mod 4 eq 1 select (2^(vu div 2)*(r mod 8 in [1,7] select 1 else -1)) else 0;
end function;

CN := func<N,u,t,n|&*[ZZ|a[1] eq 2 select CN2(a[2],vu,t,n) else CNp(a[1],a[2],vu,t,n) where vu:=Valuation(u,a[1]) : a in Factorization(N)]>;
SNbase := func<N,t,n|&*[ZZ|a[1] eq 2 select SN2base(a[2],t,n) else SNpbase(a[1],a[2],t,n) : a in Factorization(N)]>;

//Gpk := func<k,t,n|k eq 2 select 1 else (Coefficient(1/(1-t*R.1+n*R.1^2),k-2) where R := PowerSeriesRing(Parent(t):Precision:=k-1))>;

function Gpk(k,t2,n) // Given, k,t^2,n, returns [x^{k-2}] 1/(1-tx+nx^2), i.e. the coefficient of x^{k-2} in 1/(1-tx+nx^2)
    if k eq 2 then return 1; end if;
    a:=1; b:=t2-n;
    for w in [6..k by 2] do c := (t2-2*n)*b - n^2*a; a:=b; b:=c; end for;
    return b;
end function;

function Gpkl(k,t,n,l) // Given k,t,n,l returns Gpk(k,t^2l^2,ln)/l^(k/2-1) = Gpk(k,t^2l)
    return Gpk(k,t^2*l,n);
end function;

ss := func<D|D eq 0 select 0 else (s where _,s:=SquareFree(D))>;
ssr := func<D|D eq 0 select 0 else &*PrimeDivisors(ss(D))>;
/*
for a in [1..12] do for n in [1..2^(a+2)] do N:=2^a; b:=Floor(2*Sqrt(n)); for t in [-b..b] do D:=t^2-4*n; for u in Divisors(GCD(N,ss(D))) do i:=Valuation(u,2);
j := SN2(a,0,t,n); if j eq 0 then continue; end if;
j := ExactQuotient(CN(N,u,t,n),j);
if i eq 0 then assert j eq 1; continue; end if;
ai2 := a mod 2 eq i mod 2;
b:=Valuation(D,2); r := D ne 0 select (D div 2^b) mod 8 else 0;
if i le b-a-2 and ai2 then assert j eq (a eq i select 2^Ceiling(i/2) else 2^(Ceiling(i/2)-1)); continue; end if;
if i eq b-a-1 and ai2 then assert j eq -2^(Ceiling(i/2)-1); continue; end if;
if i eq b-a and ai2 then assert j eq (a eq i and r mod 4 eq 1 select 2^(Ceiling(a/2)) else 2^(Ceiling(i/2)-1)*(r mod 4 eq 1 select 1 else -1)); continue; end if;
if i eq b-a+1 and not ai2 and r mod 4 eq 1 then assert j eq 2^(i div 2)*KroneckerSymbol(r,2); continue; end if;
assert j eq 0;
end for; end for; end for; print N; end for;
*/

/*
for N in PrimePowers(1000) do for n in [1..4*N] do b:=Floor(2*Sqrt(n)); for t in [-b..b] do D:=4*n-t^2; for u in Divisors(GCD(N,ss(D))) do
a := CN(N,u,t,n); b := CNfast(N,u,t,n);
if a ne b then print N,u,t,n,a,b; end if;
assert a eq b;
end for; end for; end for; print N; end for;
*/

PhiNl := func<N,l,a,d|EulerPhi(l)/l*&+[ZZ|EulerPhi(GCD(r,ll div r)):r in Divisors(ll)|GCD(r,a) eq 1 and GCD(ll div r,d) eq 1 and IsDivisibleBy(a-d,GCD(r,ll div r))] where ll:=N div l>;
sigma1N := func<N,n|&+[ZZ|n div d:d in Divisors(n)|GCD(N,d) eq 1]>;

// Theorem 4 of Popa computing the trace of T_n W_l on S_k(N), see https://doi.org/10.1007/s40687-018-0125-5
popa := func<k,N,n,l|-((A div 12)+B) div 2 + (k eq 2 select sigma1N(N,n) else 0)
                     where A := &+[ZZ|Gpk(k,t^2*l,n)*SNbase(ll,t*l,nl)*&+[ZZ|H12(D div (u*uu)^2)*CN(ll,uu,t*l,nl)*MoebiusMu(u):u in Divisors(l),uu in Divisors(ll)|D mod (u*uu)^2 eq 0]
                                      where D:= 4*nl-t^2*l^2: t in [-b..b]] where b := Floor(Sqrt(4*nl)/l) where ll := N div l
                     where B := &+[ZZ|Min(a,d)^(k-1)/lw2*PhiNl(N,l,a,d) where a:=nl div d:d in Divisors(nl)|(d+(nl div d)) mod l eq 0]
                     where nl := n*l
                     where lw2 := l^(w div 2)
                     where w := k-2>;

// D = N*(4p-t^2N), q|N,q^2|D -> q^2|N or (q=2|N) or (q=p|N)

sfdivtab := [IsSquarefree(n) select Divisors(n) else []:n in [1..30029]];
mutab := [MoebiusMu(n): n in [1..30029]];

skNn := func<k,N,n|ExactQuotient(&+[ZZ|(a^2 eq Nn select 1 else 2)*a^(k-1):a in Divisors(Nn)|a le d and (a+d) mod N eq 0 where d:=Nn div a]*EulerPhi(N),N^(k div 2)) where Nn := N*n>;
skNn1 := func<k,N,n|ExactQuotient(&+[ZZ|(Min(a,d)^2 div N)^(k div 2-1)*Min(a,d) where d:=Nn div a:a in Divisors(Nn)|(a+d) mod N eq 0 where d:=Nn div a]*EulerPhi(N),N) where Nn := N*n>;
skNn2 := func<k,N,n|nn *s eq n select ((b and (a+a) mod r eq 0 select a^(k-1) else 0 where b,a:=IsSquare(nn)) + 2*&+[ZZ|a^(k-1): a in Divisors(nn)|a lt d and (a+d) mod r eq 0 where d:= nn div a])*EulerPhi(r*s)*s^(k div 2 -1) else 0 where nn := n div s where s,r := Squarefree(N)>;

mk := func<k,M,N|&+[ZZ|Min(u,M div u)^(k-1):u in Divisors(M)|(u+ M div u) mod N eq 0]>;
mpe:= func<k,p,e,N|(N in [1,2] and e mod 2 eq 0 select p^((e div 2)*(k-1)) else 0)+ 2*&+[ZZ|p^(i*(k-1)):i in [0..(e+1) div 2 -1]|(p^(e-2*i)+1) mod N eq 0]>;
skN1 := func<k,N|N eq 1 or N eq 4 select 1 else 0>;
skNp := func<k,N,p|b select (IsDivisibleBy(p+1,r) select 2*EulerPhi(r) else 0) else (N eq p or (N eq 4*p and N ne 8) select (p-1)*p^(k div 2 -1) else (N eq 8 and p eq 2 select 2^(k div 2) else 0)) where b,r:=IsSquare(N)>;
skNsf := func<k,N,n|n mod N eq 0 select (EulerPhi(N)*N^(k div 2-1)*&+[ZZ|Min(a,M div a)^(k-1):a in Divisors(M)] where M:= n div N) else 0>;
skNcoprime := func<k,N,n|b and r le n+1 select EulerPhi(r)*mk(k,n,r) else 0 where b,r:=IsSquare(N)>;

function skNp2(k,N,p)
    if p eq 2 and N eq 16 then return 2^k; end if;
    a := Valuation(N,p); if a gt 2 then return 0; end if;
    b,u := IsSquare(N div p^a); if not b then return 0; end if;
    if a eq 0 then return (p^2+1) mod u eq 0 select EulerPhi(u)*(2+(u le 2 select p^(k-1) else 0)) else 0; end if;
    if a eq 1 then return (p+1) mod u eq 0 select 2*(p-1)*EulerPhi(u)*p^(k div 2 -1) else 0; end if;
    return u le 2 select (p-1)*p^(k-1) else 0;
end function;
skNpe := func<k,N,p,e|p eq 2 and N eq 2^(e+2) select 2^(e*(k div 2)) else (b and a le e and u le p^(e-a)+1 select EulerPhi(u*p^a)*p^(a*(k div 2-1))*mpe(k,p,e-a,u) else 0 where b,u:=IsSquare(N div p^a) where a:=Valuation(N,p))>;

function popaNbase(k,N,n) // l = N, l' = 1 in Theorem 4 of Popa https://doi.org/10.1007/s40687-018-0125-5
    l := N; ln := l*n; b := Floor(2*Sqrt(ln)/l);
    S1 := ExactQuotient(&+[ZZ|&+[ZZ|MoebiusMu(u)*H12(D div (u*u)):u in Divisors(GCD(l,ssr(D)))]*Gpk(k,t^2*l,n) where D:=4*ln-t^2*l^2:t in [-b..b]],12);
    S2 := ExactQuotient(&+[ZZ|(Min(a,d)^2 div l)^(k div 2-1)*Min(a,d) where a:=ln div d:d in Divisors(ln)|(d+(ln div d)) mod l eq 0]*EulerPhi(l),l);
    ret := -ExactQuotient(S1+S2,2) + (k eq 2 select sigma1N(N,n) else 0);
    return ret;
end function;

phiD1 := func<D,n|&*[ZZ|1+((a[1]^a[2]-1) div (a[1]-1))*(a[1]-KroneckerSymbol(D,a[1])):a in Factorization(n)]>;

function psk(k,N,n)
    s,r := Squarefree(N*n); r := GCD((r*s),N); s := ExactQuotient(r*r,N);
    if n mod s ne 0 then return 0; end if;
    nn := n div s; NN := N div r;
    if NN gt nn+1 then return 0; end if;
    t := z and 2*a mod NN eq 0 select a^(k-1) else 0 where z,a:=IsSquare(nn);
    return (t + 2*&+[ZZ|a^(k-1): a in Divisors(nn)|a lt d and (a+d) mod NN eq 0 where d:= nn div a])*EulerPhi(r)*s^(k div 2 - 1);
end function;

function popaN(k,N,n) // l = N, l' = 1 in Theorem 4 of Popa https://doi.org/10.1007/s40687-018-0125-5
    n4 := 4*n; b := Floor(Sqrt(n4/N)); if b^2*N eq n4 then b -:= 1; end if;
    function perpN(u) repeat d := GCD(u,N); u div:= d; until d eq 1; return u; end function;
    ww := func<t2N|(IsDiscriminant(((t2N-n4)*N) div v^2) select v else v div 2) where v:=perpN(u) where _,u := Squarefree((t2N-n4) div d)> where d:=GCD(N,n4);
    S := 2*&+[ZZ|phiD1(D1,w)*h6(D1)*Gpk(k,t2N,n) where D1:=(t2N-4*n)*N div w^2 where w:=ww(t2N) where t2N:=t^2*N : t in [1..b]]
         + (phiD1(D1,w)*h6(D1)*Gpk(k,0,n) where D1 := -4*n*N div w^2 where w:=ww(0)) - (N eq 1 and IsSquare(n) select n^(k div 2-1)*(k-1) else 0);
    S := ExactQuotient(S,6) + psk(k,N,n);
    ret := -ExactQuotient(S,2) + (k eq 2 select sigma1N(N,n) else 0);
    return ret;
end function;

function popaN1(k,N) // case l = N, l' = 1, n = 1 in Theorem 4 of Popa https://doi.org/10.1007/s40687-018-0125-5, implements (3.1) in traceform.tex
    k2 := (k eq 2 select 1 else 0);
    if N eq 1 then return k div 12 - (k mod 12 eq 2 select 1 else 0) + k2; end if;
    if N eq 2 then return (k8 eq 2 select -1 else (k8 eq 0 select 1 else 0)) + k2 where k8 := k mod 8; end if;
    if N eq 3 then return ((k div 2) mod 3) eq 2 select 0 else ((k mod 4) eq 0 select 1 else -1) + k2; end if;
    if N eq 4 then return (k mod 4 eq 2 select -1 else 0) + k2; end if;
    ksign := (k mod 4 eq 0 select 1 else -1);
    hstar := N mod 8 eq 3 select 4*h6(-N) else (N mod 8 eq 7 select 2*h6(-N) else h6(-4*N));
    return ksign*ExactQuotient(hstar,12) + k2;
end function;

function pskp(k,N,p)
    if N eq 8 and p eq 2 then return 2^(k div 2);
    elif N eq p or N eq 4*p then return (p-1)*p^(k div 2-1);
    end if;
    b,u := IsSquare(N);
    return b and (p+1) mod u eq 0 select 2*EulerPhi(u) else 0;
end function;

cond := func<D|ZZ!Sqrt(D div FundamentalDiscriminant(D))>;

function popaNp(k,N,p)
    n := p; n4 := 4*p; b := Floor(Sqrt(n4/N)); if b^2*N eq n4 then b -:= 1; end if;
    ww := func<t2N|w where w := (IsEven(v) and (((n4-t2N) div v^2)*N mod 4) in [1,2]) select v div 2 else v
                     where _,v := Squarefree((t2N-n4) div ((p gt 2 and N mod p eq 0 select p else 1)*(IsEven(N) select 2^Valuation(t2N-n4,2) else 1)))>;
    S := 2*&+[ZZ|phiD1(D1,w)*h6(D1)*Gpk(k,t2N,n) where D1:=(t2N-n4)*N div w^2 where w:=ww(t2N) where t2N:=t^2*N : t in [1..b]]
         + (phiD1(D1,w)*h6(D1)*(-n)^(k div 2 - 1) where D1 := -n4*N div w^2 where w:=(IsEven(N) or (p*N mod 4) ne 3) select 1 else 2);
    S := ExactQuotient(S,6) + pskp(k,N,p);
    ret := -ExactQuotient(S,2) + (k eq 2 select (N mod p eq 0 select p else p+1) else 0);
    return ret;
end function;

function pskp2(k,N,p)
    if N eq 16 and p eq 2 then return 2^k; end if;
    p2 := p*p;
    if N eq p2 or N eq 4*p2 then return (p-1)*p^(k-1); end if;
    if N mod p eq 0 then
        b,u := IsSquare(N div p);
        return b and (p+1) mod u eq 0 select 2*EulerPhi(u)*(p-1)*p^(k div 2-1) else 0;
    else
        b,u := IsSquare(N);
        return b and (p2+1) mod u eq 0 select EulerPhi(u)*(2+(2 mod u eq 0 select p^(k-1) else 0)) else 0;
    end if;
end function;

function popaNp2(k,N,p)
    p2 := p*p; n := p2; n4 := 4*n; b := Floor(Sqrt(n4/N)); if b^2*N eq n4 then b -:= 1; end if;
    ww := func<t2N|w where w := (IsEven(v) and (((n4-t2N) div v^2)*N mod 4) in [1,2]) select v div 2 else v
                     where _,v := Squarefree((t2N-n4) div ((p gt 2 and N mod p eq 0 select p^Valuation(t2N-n4,p) else 1)*(IsEven(N) select 2^Valuation(t2N-n4,2) else 1)))>;
    S := 2*&+[ZZ|phiD1(D1,w)*h6(D1)*Gpk(k,t2N,n) where D1:=(t2N-n4)*N div w^2 where w:=ww(t2N) where t2N:=t^2*N : t in [1..b]]
         + (phiD1(D1,w)*(N mod p eq 0 and p gt 2 and N gt 1 select p*h6(D1 div p2) else h6(D1))*Gpk(k,0,n) where D1 := -n4*N div w^2 where w:=ww(0)) - (N eq 1 select p^(k-2)*(k-1) else 0);
    S := ExactQuotient(S,6) + pskp2(k,N,p);
    ret := -ExactQuotient(S,2) + (k eq 2 select (N mod p eq 0 select p2 else p2+p+1) else 0);
    return ret;
end function;

t1 := func<k,N|&+[ZZ|MoebiusMu(d)*popaN1(k,N div (d*d)):d in Divisors(ssr(N))]>;
t2 := func<k,N,p|N mod p ne 0 select 0 else p^(k div 2 - 1)*(p - (Valuation(N,p) eq 1 select 1 else 0))*&+[ZZ|t1(k,d):d in Divisors(N div p)|IsSquare(N div (d*p))]>;

function newpopaNpbase(k,N,p)
    s := ssr(N); if s mod p eq 0 then s div:= p; end if;
    return N mod p eq 0 select &+[ZZ|MoebiusMu(d)*(popaNp(k,M,p)-t2(k,M,p)) where M:=N div (d*d):d in Divisors(s)]
                          else &+[ZZ|MoebiusMu(d)*popaNp(k,N div (d*d),p):d in Divisors(s)];
end function;

function newpopaN1(k,N)
    phimu := func<D,u|&*[ZZ|p-1-KroneckerSymbol(D,p):p in PrimeDivisors(u)]>;
    g := func<N|N mod 4 eq 3 select (N mod 8 eq 3 select 4/3 else 2) else 1>;
    gg := func<N|N mod 32 eq 28 select 0 else (N mod 32 eq 12 select 2/3 else g(N))>;
    u := ssr(N); NN := N div u^2; D := -4*NN;
    plus1 := k eq 2 and u eq 1 select 1 else 0;
    ksign := k mod 4 eq 0 select 1 else -1;
    k2 := k eq 2 select 1 else 0;
    if NN eq 1 and IsEven(u) then
        return MoebiusMu(u)*(popaN1(k,1)-popaN1(k,4)) + ExactQuotient(phimu(D,u)+MoebiusMu(u),4)*ksign;
    elif NN le 4 then
        mu := MoebiusMu(u); phi:=phimu(D,u);
        ret := MoebiusMu(u)*(popaN1(k,NN)-k2) + ExactQuotient((gg(N)*phi-g(NN)*MoebiusMu(u))*h6(D),12)*ksign + plus1;
        if NN eq 1 then
            assert ret eq mu*(k div 12 - (k mod 12 eq 2 select 1 else 0)) + ExactQuotient(phi-mu,4)*ksign + plus1;
        elif NN eq 2 then
            assert ret eq mu*((k8 eq 2 select -1 else (k8 eq 0 select 1 else 0)) where k8 := k mod 8) + ExactQuotient(phi-mu,2)*ksign + plus1;
        elif NN eq 3 then
            assert ret eq mu*(((k div 2) mod 3) eq 2 select 0 else ((k mod 4) eq 0 select 1 else -1)) + ExactQuotient(phi*gg(N)*3-4*mu,6)*ksign + plus1;
        elif NN eq 4 then
            assert ret eq mu*(k mod 4 eq 2 select -1 else 0) + ExactQuotient(phi-mu,2)*ksign + plus1;
        end if;
        return ret;
    end if;
    return ExactQuotient(ZZ!(gg(N)*phimu(D,u)*h6(D)),12)*ksign + plus1;
end function;

function WNp(k,N,p)
    e := Valuation(N,p); if e eq 0 then return 0; end if;
    if e eq 1 then return p^(k div 2 -1)*(1-p)*newpopaN1(k,N div p); end if;
    return -p^(k div 2) * &+[newpopaN1(k,N div p^(2*i+1)):i in [0..(e-1) div 2]];
end function;

function newpopaNp(k,N,p)
    s := ssr(N); if s mod p eq 0 then s div:= p; end if;
    return &+[ZZ|MoebiusMu(d)*popaNp(k,N div (d*d),p):d in Divisors(s)] + (N mod p eq 0 select WNp(k,N,p) else 0);
end function;

function newpopaNp2(k,N,p)
    if N mod p^2 eq 0 then return 0; end if;
    s := ssr(N);
    return &+[ZZ|MoebiusMu(d)*popaNp2(k,N div (d*d),p):d in Divisors(s)] + (N mod p eq 0 select (1-p)*p^(k div 2-1)*newpopaNp(k,N div p,p) else 0);
end function;

// (5.23) alpha_{Q,n}(d) of Assaf specialized to the situation where Q=N
// In this case case d divides q and alpha_{Q,n}(d) = 0 unless (n,d)=1 and d is the square of a squarefree integer s, in which case alpha_{Q,n}(d) = mu(s)
rawamu := func<n,d|&*[ZZ|a[2] eq 2 and n mod a[1] ne 0 select -1 else 0:a in Factorization(d)]>;
amu := func<n,d|GCD(n,d) eq 1 and  b and IsSquarefree(s) select MoebiusMu(s) else 0 where b,s :=IsSquare(d)>;

SNd := func<N,d|[NN:NN in Divisors(N)|(N div NN) mod d eq 0 and GCD(d,NN) eq 1]>;
SNndnn := func<N,n,d,nn|[NN:NN in SNd(N,d)|GCD(N div NN,d*n) eq nn and IsSquare(N div (NN*nn))]>;
SNQdnn := func<N,n,d,nn|SNndnn(N,GCD(N,n),GCD(N,d),GCD(N,nn))>;
SNn := func<N,n|Set(&cat[&cat[SNQdnn(N,n,d,nn):d in Divisors(nn)|nn div GCD(nn,N) eq (d div (GCD(d,N)))^2]:nn in Divisors(n)|nn gt 1])>;


/*
function newpopaNp(k,N)
    dd := Divisors(ssr(N)); c := #dd; md := [MoebiusMu(d):d in dd];  f := [popaNp(k,N div (d*d)): d in dd];
    return func<p|N mod p eq 0 select &+[ZZ|md[i]*(f[i](p)-t2(k,N div (dd[i]*dd[i]),p)) : i in [1..c] | dd[i] mod p ne 0]
                                 else &+[ZZ|md[i]*f[i](p):i in [1..c]]>;
end function;
*/

function popa1(k,N,n) // l = 1, l' = N in Theorem 4 of Popa  https://doi.org/10.1007/s40687-018-0125-5
    b := Floor(2*Sqrt(n));
    if k eq 2 then
        S1 := &+[ZZ|&+[ZZ|H12(D div (u*u))*CN(N,u,t,n):u in Divisors(GCD(N,ss(D)))]*SNbase(N,t,n) where D:=4*n-t^2:t in [-b..b]] div 12;
    else
        S1 := &+[ZZ|&+[ZZ|H12(D div (u*u))*CN(N,u,t,n):u in Divisors(GCD(N,ss(D)))]*SNbase(N,t,n)*Gpk(k,t^2,n) where D:=4*n-t^2:t in [-b..b]] div 12;
    end if;
    S2 := &+[ZZ|Min(a,d)^(k-1)*&+[ZZ|EulerPhi(GCD(r,N div r)):r in Divisors(N)|GCD(r,a) eq 1 and GCD(s,d) eq 1 and IsDivisibleBy(a-d,GCD(r,s)) where s := N div r]
            where a:=n div d:d in Divisors(n)];
    ret := -(S1+S2) div 2 + (k eq 2 select sigma1N(N,n) else 0);
    //print S1,S2,ret;
    return ret;
end function;

psi:=func<N|&*[ZZ|(a[1]+1)*a[1]^(a[2]-1):a in Factorization(N)]>;
psi4:=func<N|N mod 4 eq 0 select 0 else &*[ZZ|3-p mod 4:p in PrimeDivisors(N)]>;
psi3:=func<N|N mod 9 eq 0 select 0 else &*[ZZ|(p+1) mod 3:p in PrimeDivisors(N)]>;
epsi:=func<N|&*[ZZ|2 + 2*&+[ZZ|(a[1]-1)*a[1]^(e-1):e in [1..(a[2]-1) div 2]] + (IsEven(a[2]) select (a[1]-1)*a[1]^(a[2] div 2-1) else 0):a in Factorization(N)]>;

function popa11(k,N) // l = 1, l' = N, n = 1 in Theorem 4 of Popa  https://doi.org/10.1007/s40687-018-0125-5
    b := 2;
    if k eq 2 then
        S1 := (6*psi4(N) + 8*psi3(N) - 2*psi(N)) div 12;
    else
        S1 := (6*psi4(N)*Gpk(k,0,1) + 8*psi3(N)*Gpk(k,1,1) - 2*psi(N)*Gpk(k,4,1)) div 12;
    end if;
    S2 := epsi(N);
    ret := -(S1+S2) div 2 + (k eq 2 select 1 else 0);
    return ret;
end function;


function popa1p(k,N,p) // l = 1, l' = N, n = p prime in Theorem 4 of Popa  https://doi.org/10.1007/s40687-018-0125-5
    b := Floor(2*Sqrt(p));
    qq := PrimeDivisors(N);
    if k eq 2 then
        S1 := &+[ZZ|s eq 0 select 0 else s*&+[ZZ|H12(D div (u*u))*CN(N,u,t,p):u in Divisors(GCD(N,ss(D)))] where s:=SNbase(N,t,p) where D:=4*p-t^2:t in [-b..b]|&and[KroneckerSymbol(t^2-4*p,q) ge 0:q in qq]] div 12;
    else
        S1 := &+[ZZ|s eq 0 select 0 else s*&+[ZZ|H12(D div (u*u))*CN(N,u,t,p):u in Divisors(GCD(N,ss(D)))]*SNbase(N,t,p)*Gpk(k,t^2,p) where s:=SNbase(N,t,p) where D:=4*p-t^2:t in [-b..b]] div 12;
    end if;
    S2 := N mod p eq 0 select &+[ZZ|EulerPhi(GCD(r,N div r)):r in Divisors(N)|(r mod p ne 0 or s mod p ne 0) and IsDivisibleBy(p-1,GCD(r,s)) where s := N div r]
                       else 2*&+[ZZ|EulerPhi(GCD(r,N div r)):r in Divisors(N)|IsDivisibleBy(p-1,GCD(r,s)) where s := N div r];
    ret := -(S1+S2) div 2 + (k eq 2 select p+(N mod p eq 0 select 0 else 1) else 0);
    //print S1,S2,ret;
    return ret;
end function;

// Formula to compute newpopa1 from popa1 is given by Lemma 10 in Child21 https://link.springer.com/article/10.1007/s40993-021-00302-9
// This is the function mu * mu[m] in Tomohiko https://arxiv.org/abs/1108.4774 (here * denotes convolution and mu[m] is mu on inputs coprime to m and 0 ow)
beta := func<m,N|&*[ZZ|a[2] eq 1 select d-2 else (a[2] eq 2 select 1-d else 0) where d:=m mod a[1] eq 0 select 1 else 0:a in Factorization(N)]>;
beta1 := func<N|&*[ZZ|a[2] eq 1 select -2 else (a[2] eq 2 select 1 else 0):a in Factorization(N)]>; // mu * mu
betap := func<p,N|&*[ZZ|a[1] eq p select (a[2] eq 1 select -1 else 0) else (a[2] eq 1 select -2 else (a[2] eq 2 select 1 else 0)):a in Factorization(N)]>;

function newpopa1(k,N,n)
    return &+[d^(k-1)*&+[ZZ|beta(n div d^2, N div M)*popa1(k,M,n):M in Divisors(N)]:d in Divisors(GCD(Squarefree(N),ssr(n)))];
end function;

function newpopa11(k,N)
    return &+[ZZ|beta1(N div M)*popa11(k,M):M in Divisors(N)];
end function;

function tomo1(k,N) // implements the formula for dim S_k on page 3 of https://arxiv.org/abs/1108.4774
    Q := Factorization(N);
    ed := 1; e2 := 1; e3 := 1; e0 := 1;
    for q in Q do p := q[1]; n := q[2];
        ed *:= p^n+p^(n-1);
        e2 *:= p eq 2 select (n eq 1 select 1 else 0) else 3 - p mod 4;
        e3 *:= p eq 3 select (n eq 1 select 1 else 0) else 2*(2 - p mod 3);
        e0 *:= p^(n div 2) + p^((n-1) div 2);
    end for;
    return ((k-1)*ed + (k mod 4 eq 2 select -3 else 3)*e2 - 4*(k mod 3 - 1)*e3 - 6*e0) div 12 + (k eq 2 select 1 else 0);
end function;

function newtomo1(k,N) // implements the formula for dim S_k^new on page 3 of https://arxiv.org/abs/1108.4774, this is crazy fast
    Q := Factorization(N);
    ed := 1; e2 := 1; e3 := 1; e0 := 1;
    for q in Q do
        p := q[1]; n := q[2];
        if n eq 1 then ed *:= p-1; e2 *:= 1 - p mod 4; e3 *:= (p+1) mod 3 - 2; e0 := 0;
        elif n eq 2 then ed *:= p^2-p-1; e2 *:= p eq 2 select -1 else p mod 4 - 2; e3 *:=  p eq 3 select -1 else 1 - (p+1) mod 3; e0 *:= p-2;
        elif n eq 3 then ed *:= (p-1)*(p^2-1); e2 *:= p eq 2 select 1 else 0; e3 *:= p eq 3 select 1 else 0; e0 *:= 0;
        else ed *:= p^(n-3)*(p-1)*(p^2-1); e2 := 0; e3 := 0; e0 *:= n mod 2 eq 1 select 0 else p^(n div 2 -2)*(p-1)^2;
        end if;
    end for;
    //print ed,e2,e3,e0;
    //print (k-1), 3*(k mod 4 eq 2 select -1 else 1), - 4*(k mod 3 - 1), -6;
    return ((k-1)*ed + (k mod 4 eq 2 select -3 else 3)*e2 - 4*(k mod 3 - 1)*e3 - 6*e0) div 12 + (k eq 2 select MoebiusMu(N) else 0);
end function;

/*
vpe := func<p,e|
    e eq 1 select Vector([p-1,1-p mod 4, (p+1) mod 3-2, 0]) else
    (e eq 2 select Vector([p^2-p-1, p mod 4-2-(p eq 2 select 1 else 0), 1-(p+1) mod 3 - (p eq 3 select 1 else 0), p-2]) else
     (e eq 3 select Vector([(p-1)*(p^2-1), p eq 2 select 1 else 0, p eq 3 select 1 else 0, 0])
      else Vector([p^(e-3)*(p^2-1)*(p-1),0,0,IsEven(e) select p^(e div 2 -2)*(p-1)^2 else 0])))>;
vN := func<N|N eq 1 select Vector([1,1,1,1]) else &*[vpe(q[1],q[2]):q in Factorization(N)]>;
wk := func<k|Vector([k-1,(k mod 4 eq 0 select 6 else 0) - 3, 4*(1-k mod 3), -6])>;
t1 := func<k,N|&+[d[i]:i in [1..4]] div 12 + (k eq 2 select MoebiusMu(N) else 0) where d:=vN(N)*wk(k)>;
*/



function atkl(t,k,l) assert IsPrime(l) and (t^2 le 4*l or Abs(t) eq (l+1)); return Abs(t) eq l+1 select 1/(2*(l-1)) else Gpk(k,t^2,l); end function;
function htl(t,l) D:=t^2-4*l; w := IsSquare(D/-3) select 6 else (IsSquare(D/-4) select 4 else 2);  return D lt 0 select ClassNumber(D)/w else 1; end function;
function Kd(d,N)
    return &*[ZZ|(n eq 1 select KroneckerSymbol(d,p)-1 else
                  (n eq 2 select (d mod p eq 0 select -1 else -KroneckerSymbol(d,p)) else
                   (n eq 3 and d mod p eq 0 select 1 else 0))) where p:=q[1] where n:=q[2] : q in Factorization(N)];
end function;

function ctlraw(t,l,phi,N)
    D := t^2-4*l; d := FundamentalDiscriminant(D); m := ZZ!Sqrt(D/d); psi := ExactQuotient(m,phi);
    Q := Factorization(N);
    return &*[ZZ|#{z:z in Integers(psi^2*q[1]^q[2])|z^2-t*z+l eq 0 and Integers(q[1])!z ne 0} +
                 (d*phi) mod q[1] eq 0 select 0 else #{z:z in Integers(psi^2*q[1]^(q[2]+1))|z^2-t*z+l eq 0 and Integers(q[1])!z ne 0}:q in Q];
end function;


function nutl(t,l,N:fast:=true)
    assert IsPrime(l) and N mod l^2 ne 0;
    if t mod GCD(N,l) ne 0 then return 0; end if;
    D := t^2-4*l; assert D lt 0;
    d := FundamentalDiscriminant(D); _,m := IsSquare(D div d);
    if m eq 1 and fast then return Kd(d,N); end if;
    if IsPrime(m) and fast then
        v := Valuation(N,m);
        s := KroneckerSymbol(d,m);
        if v eq 0 then mm := (m+1-s);
        elif v eq 1 then mm := s-1;
        elif v eq 2 then mm := m^2-2*m-1+s;
        elif v eq 3 then mm := s eq 0 select 1-m^2 else (m-s)*(m-1)*(s-1);
        elif v eq 4 then mm := s eq 0 select m(1-m) else -(m-s)*m*s;
        elif v eq 5 then mm := s eq 0 select m^2 else 0;
        else mm := 0;
        end if;
        return Kd(d,N div m^v)*mm;
    else
        assert false;
        //btl:= func<phi|&*[ZZ|p[1]^(p[2]-1)*(p[1]-KroneckerSymbol(d,p[1])):p in Factorization(phi)]>;
        //return &+[btl(phi)*&+[ctlraw(t,l,phi,a)*betap(l,N div a):a in Divisors(N)]:phi in Divisors(m)];
    end if;
end function;

function Kd(d,N)
    return &*[ZZ|(n eq 1 select KroneckerSymbol(d,p)-1 else
                  (n eq 2 select (d mod p eq 0 select -1 else -KroneckerSymbol(d,p)) else
                   (n eq 3 and d mod p eq 0 select 1 else 0))) where p:=q[1] where n:=q[2] : q in Factorization(N)];
end function;

kn2 := [0,1,0,1,0,-1,0,-1];
kn3 := [0,1,-1];
kn4 := [0,1,0,-1];
kn7 := [0,1,1,-1,1,-1,-1];
kn11 := [0,1,-1,1,1,1,-1,-1,-1,1,-1];

function newtomo2(k,N) // implements Proposition 13 of https://arxiv.org/abs/1108.4774
    if N mod 4 eq 0 then return 0; end if;
    Q := Factorization(N);
    Kn2 := 1; Kn4 := 1; Kn7 := 1;
    for q in Q do p := q[1]; n := q[2];
        if n eq 1 then Kn2 *:= kn2[p mod 8 + 1] -1; Kn4 *:= kn4[p mod 4 + 1] - 1; Kn7 *:= kn7[p mod 7 + 1] - 1;
        elif n eq 2 then Kn2 *:= p eq 2 select -1 else -kn2[p mod 8 + 1];
                         Kn4 *:= p eq 2 select -1 else -kn4[p mod 4 + 1];
                         Kn7 *:= p eq 7 select -1 else -kn7[p mod 7 + 1];
        elif n eq 3 and p eq 2 then Kn7 := 0;
        elif n eq 3 and p eq 7 then Kn2 := 0; Kn4 := 0;
        else Kn2 := 0; Kn4 := 0; Kn7 := 0;
        end if;
    end for;
    b,m := IsSquare(N); K1 := b select MoebiusMu(m) else 0;
    if k eq 2 then dk2 := MoebiusMu(N) * (N mod 2 eq 0 select 1 else 3); else dk2 := 0; end if;
    return -(-2)^(k div 2 - 1)*(Kn2 + (k mod 8 in [0,2] select 1 else -1)*Kn4) div 2 - Gpk(k,1,2)*Kn7 - K1 + dk2;
end function;

function newtomo3(k,N) // implements Proposition 15 of https://arxiv.org/abs/1108.4774
    if N mod 9 eq 0 then return 0; end if;
    v2 := Valuation(N,2);
    Q := Factorization(N);
    Kn2 := 1; Kn3 := 1; Kn11 := 1;
    Nu03 := v2 eq 0 select 4 else (v2 lt 3 select -2 else (v2 eq 3 select -6 else (v2 eq 4 select 6 else 0)));
    for q in Q do p := q[1]; n := q[2];
        if n eq 1 then Kn2 *:= kn2[p mod 8 + 1] -1; Kn3 *:= kn3[p mod 3 + 1] - 1; Kn11 *:= kn11[p mod 11 + 1] - 1; Nu03 *:= p eq 2 select 1 else kn3[p mod 3 + 1] - 1;
        elif n eq 2 then Kn2 *:= p eq 2 select -1 else -kn2[p mod 8 + 1];
                         Kn3 *:= p eq 3 select -1 else -kn3[p mod 3 + 1];
                         Kn11 *:= p eq 11 select -1 else -kn11[p mod 11 + 1];
                         Nu03 *:= p eq 2 select 1 else (p eq 3 select -1 else -kn3[p mod 3 + 1]);
        elif n eq 3 and p eq 2 then Kn3 := 0; Kn11 := 0;
        elif n eq 3 and p eq 3 then Kn2 := 0; Kn11 := 0;
        elif n eq 3 and p eq 11 then Kn2 := 0; Kn3 := 0; Nu03 := 0;
        else Kn2 := 0; Kn3 := 0; Kn11 := 0; if p ne 2 then Nu03 := 0; end if;
        end if;
    end for;
    b,m := IsSquare (N div 2^v2);
    Nu43 := b select MoebiusMu(m) * (v2 eq 0 select 2 else (v2 eq 4 select -2 else 0)) else 0;
    b,m := IsSquare(N); K1 := b select MoebiusMu(m) else 0;
    if k eq 2 then dk2 := MoebiusMu(N) * (N mod 3 eq 0 select 1 else 4); else dk2 := 0; end if;
    //print Nu03, Nu43, Kn2, Kn3, Kn11, dk2;
    return -((-3)^(k div 2 - 1)*(Nu03 + 2 * (k mod 6 in [0,2] select 1 else -2)*Kn3)) div 6 - Gpk(k,1,3)*Kn11 - Gpk(k,4,3)*Kn2 - Nu43 div 2 + dk2;
end function;

function newtomobadp(k,N,p) // implements Propositions 18 of https://arxiv.org/abs/1108.4774 for l=p prime using newtomo2,newtomo3 to handle l=p<=3 where p <= 2sqrt(p) is possible
    // assert N mod p eq 0;
    if N mod p^2 eq 0 then return 0; end if;
    if p eq 2 then return newtomo2(k,N); elif p eq 3 then return newtomo3(k,N); end if;
    if p mod 4 eq 1 then
        a := ExactQuotient(Kd(-4*p,N div p)*ClassNumber(-4*p),2);
    else
        v2 := Valuation(N,2); s := p mod 8 eq 3 select -1 else 1;
        if v2 eq 0 then b := 3-s; elif v2 eq 1 or v2 eq 2 then b := s-1; elif v2 eq 3 then b := (2-s)*(s-1); elif v2 eq 4 then b := -2*(2-s)*s; else b:=0; end if;
        a := b eq 0 select 0 else ExactQuotient(Kd(-p,N div (p*2^v2))*b*ClassNumber(-p),2);
    end if;
    return a*(-p)^(k div 2 -1) + (k eq 2 select MoebiusMu(N) else 0);
end function;

function newpopa1p(k,N,p)
    return N mod p^2 eq 0 select 0 else &+[ZZ|betap(p, N div M)*popa1p(k,M,p):M in Divisors(N)];
end function;

// Skoruppa-Zagier formulas from SZ88 https://link.springer.com/article/10.1007/BF01394347
// Note that SZ use m for the level N in Popa, they use l for the Hecke operator T_l which is T_n in Popa, and they use n for the Atkin-Lehner W_n which is W_l in Popa
// also note that H_1(D) = H(|D|) and that

Hn := func<n,D|IsDivisibleBy(D,a2b2) select ZZ!(a2b*KroneckerSymbol(N,(n div (a2b)))*H12(-N)) where N := (D div (a2b2)) else 0 where a2b := a^2*b where a2b2 := a^2*b^2 where b,a:=SquareFree(GCD(n,D))>;
Hnf := func<n|func<D|IsDivisibleBy(D,a2b2) select ZZ!(a2b*KroneckerSymbol(N,(n div (a2b)))*H12(-N)) where N := (D div (a2b2)) else 0 where a2b := a^2*b where a2b2 := a^2*b^2 where b,a:=SquareFree(GCD(n,D))>>;
delta := func<b|b select 1 else 0>;
Q := func<n|a where b,a := SquareFree(n)>;

phi1D := func<n,D|&*[1+((a[1]^a[2]-1) div (a[1]-1))*(a[1]-KroneckerSymbol(D,a[1])):a in Factorization(n)]>;
f:=func<n,D|Hn(n,D)/(2*h6(FundamentalDiscriminant(D)))>;
g := func<n,c,D|not IsDivisibleBy(c,m) select 0 else d*KroneckerSymbol(cc^2*D,n div d)*phi1D(cc,D) where cc := c div m where m := a*b where b,a:=SquareFree(d) where d:=GCD(n,c^2*D)>;

function g(n,D)
    D0 := FundamentalDiscriminant(D);
    c := ZZ!Sqrt(D div D0); assert c^2*D0 eq D;
    d := GCD(n,D);
    b,a:=SquareFree(d); m := a*b;
    if not IsDivisibleBy(c,m) then return 0; else c div:= m; end if;
    return d*KroneckerSymbol(c^2*D0,n div d)*phi1D(c,D0);
end function;

function skm(k,m,l,n)
    // assert IsDivisibleBy(m,n) and GCD(m div n, n) eq 1 and GCD(l,m) eq 1;
    mdivn := m div n;
    Hnn := Hnf(mdivn);
    A := 0; res := 0;
    if k eq 2 then
        A := &+[IsSquarefree(ndivnn) select 2*&+[ZZ|Hnn(s^2*nn2-fourlnn):s in [1..sb]] + Hnn(-fourlnn)
                                       else 2*&+[ZZ|Hnn(s^2*nn2-fourlnn):s in [1..sb]|IsSquarefree(GCD(s^2,ndivnn))]
                where sb := Floor(Sqrt(fourlnn)/nn) where ndivnn := n div nn where fourlnn := 4*l*nn where nn2 := nn*nn : nn in Divisors(n)];
        if IsSquare (mdivn) then res := NumberOfDivisors(n)*SumOfDivisors(l); end if;
    else
        A := &+[IsSquarefree(ndivnn) select 2*&+[ZZ|Gpk(k,s2*nn,l)*Hnn(s2*nn2-fourlnn) where s2:=s*s : s in [1..sb]] + Gpk(k,0,l)*Hnn(-fourlnn)
                                       else 2*&+[ZZ|Gpk(k,s2*nn,l)*Hnn(s2*nn2-fourlnn) where s2:=s*s : s in [1..sb]|IsSquarefree(GCD(s^2,ndivnn))]
                where sb := Floor(Sqrt(fourlnn)/nn) where ndivnn := n div nn where fourlnn := 4*l*nn where nn2 := nn*nn : nn in Divisors(n)];
    end if;
    A := ExactQuotient(A,12);
    B := IsPrime(l) select 2 * GCD(Q(n),l+1) * GCD(Q(mdivn),l-1)
                      else &+[ZZ|Min(ll,lll)^(k-1) * GCD(Q(n),ll + lll) * GCD(Q(mdivn),ll - lll) where lll := l div ll:ll in Divisors(l)];
    res +:= -ExactQuotient(A+B,2);
    return res;
end function;

function skp(k,m,n)
    mdivn := m div n; Hnn := Hnf(mdivn); dn := Divisors(n); Qn := Q(n); Qmdivn := Q(mdivn);
    if k eq 2 then
        if IsSquare(mdivn) then
            if IsSquarefree(n) then
                return func<l|-(A div 24)-GCD(Qn,l+1)*GCD(Qmdivn,l-1)+#dn*(l+1) where
                              A := &+[2*&+[ZZ|Hnn(s^2*nn2-fourlnn):s in [1..sb]] + Hnn(-fourlnn)
                                   where sb := Floor(Sqrt(fourlnn)/nn) where ndivnn := n div nn where fourlnn := 4*l*nn where nn2 := nn*nn : nn in dn]>;
            else
                return func<l|-(A div 24)-GCD(Qn,l+1)*GCD(Qmdivn,l-1)+#dn*(l+1) where
                              A := &+[IsSquarefree(ndivnn) select 2*&+[ZZ|Hnn(s^2*nn2-fourlnn):s in [1..sb]] + Hnn(-fourlnn)
                                               else 2*&+[ZZ|Hnn(s^2*nn2-fourlnn):s in [1..sb]|IsSquarefree(GCD(s^2,ndivnn))]
                                   where sb := Floor(Sqrt(fourlnn)/nn) where ndivnn := n div nn where fourlnn := 4*l*nn where nn2 := nn*nn : nn in dn]>;
            end if;
        else
            if IsSquarefree(n) then
                return func<l|-(A div 24)-GCD(Qn,l+1)*GCD(Qmdivn,l-1) where
                              A := ZZ!&+[IsSquarefree(ndivnn) select ZZ!2*&+[ZZ|Hnn(s^2*nn2-fourlnn):s in [1..sb]] + Hnn(-fourlnn)
                                               else 2*&+[ZZ|Hnn(s^2*nn2-fourlnn):s in [1..sb]|IsSquarefree(GCD(s^2,ndivnn))]
                                   where sb := Floor(Sqrt(fourlnn)/nn) where ndivnn := n div nn where fourlnn := 4*l*nn where nn2 := nn*nn : nn in dn]>;
            else
                return func<l|-(A div 24)-GCD(Qn,l+1)*GCD(Qmdivn,l-1) where
                              A := &+[2*&+[ZZ|Hnn(s^2*nn2-fourlnn):s in [1..sb]] + Hnn(-fourlnn)
                                   where sb := Floor(Sqrt(fourlnn)/nn) where ndivnn := n div nn where fourlnn := 4*l*nn where nn2 := nn*nn : nn in dn]>;
            end if;
        end if;
    else
        if IsSquarefree(n) then
            return func<l|-(A div 24)-GCD(Qn,l+1)*GCD(Qmdivn,l-1) where
                          A := &+[2*&+[ZZ|Gpk(k,s^2*nn,l)*Hnn(s^2*nn2-fourlnn) : s in [1..sb]] + Gpk(k,0,l)*Hnn(-fourlnn)
                               where sb := Floor(Sqrt(fourlnn)/nn) where ndivnn := n div nn where fourlnn := 4*l*nn where nn2 := nn*nn : nn in dn]>;
        else
            return func<l|-(A div 24)-GCD(Qn,l+1)*GCD(Qmdivn,l-1) where
                          A := &+[IsSquarefree(ndivnn) select ZZ!2*&+[ZZ|Gpk(k,s^2*nn,l)*Hnn(s^2*nn2-fourlnn) : s in [1..sb]] + Gpk(k,0,l)*Hnn(-fourlnn)
                                           else 2*&+[ZZ|Gpk(k,s^2*nn,l)*Hnn(s^2*nn2-fourlnn) : s in [1..sb]|IsSquarefree(GCD(s^2,ndivnn))]
                               where sb := Floor(Sqrt(fourlnn)/nn) where ndivnn := n div nn where fourlnn := 4*l*nn where nn2 := nn*nn : nn in dn]>;
        end if;
    end if;
end function;

// see page 117 of SZ https://link.springer.com/article/10.1007/BF01394347 for the definition of alpha = mu^2 * mu * mu
alpha := func<n|&*[ZZ|a[2] lt 3 select -1 else (a[2] eq 3 select 1 else 0):a in A] where A:=Factorization(n)>;

function newsz(k,m,l,n) // k = weight, m = level, l = Hecke T_l, n = Atkin-Lehner W_n
    return &+[ZZ|alpha(m div mm)*skm(k,mm,l,GCD(n,mm)):mm in Divisors(m)];
end function;

function newszN(k,m,l) // k = weight, m = level, l = Hecke T_l, Atkin-Lehner W_m
    return &+[ZZ|alpha(m div mm)*skm(k,mm,l,mm):mm in Divisors(m)];
end function;

function newszp(k,m)
    dm := Divisors(m); am := [ZZ|alpha(m div mm):mm in dm];
    skpp := [skp(k,mm):mm in dm];
    return func<l|&+[ZZ|am[i]*skpp[i](l):i in [1..#dm]]>;
end function;

function skm1(k,m,l) // n = 1
    Hnn := Hnf(m);
    A := 0; res := 0;
    if k eq 2 then
        A := 2*&+[ZZ|Hnn(s^2-4*l):s in [1..sb]] + Hnn(-4*l) where sb := Floor(2*Sqrt(l));
        if IsSquare(m) then res := SumOfDivisors(l); end if;
    else
        A := 2*&+[ZZ|Gpk(k,s2,l)*Hnn(s2-4*l) where s2:=s*s : s in [1..sb]] + ZZ!Gpk(k,0,l)*Hnn(-4*l) where sb := Floor(2*Sqrt(l));
    end if;
    A := A div 12;
    B := IsPrime(l) select 2 * GCD(Q(m),l-1)
                      else &+[ZZ|Min(ll,lll)^(k-1) * GCD(Q(m),ll - lll) where lll := l div ll:ll in Divisors(l)];
    res +:= -ExactQuotient(A+B,2);
    return res;
end function;

function skm1p(k,m) // n = 1, returns a function that takes a prime l
    Hnn := Hnf(m); Qm := Q(m);
    A := 0; res := 0;
    if k eq 2 then
        if IsSquare(m) then
            return func<l|l+1-ZZ!(2*&+[ZZ|Hnn(s^2-4*l):s in [1..sb]] + Hnn(-4*l)) div 24 - GCD(Qm,l-1) where sb:=Floor(2*Sqrt(l))>;
        else
            return func<l|-ZZ!(2*&+[ZZ|Hnn(s^2-4*l):s in [1..sb]] + Hnn(-4*l)) div 24 - GCD(Qm,l-1) where sb:=Floor(2*Sqrt(l))>;
        end if;
    else
        return func<l|-ZZ!(2*&+[ZZ|Gpk(k,s2,l)*Hnn(s2-4*l) where s2:=s*s : s in [1..sb]] + Gpk(k,0,l)*Hnn(-4*l)) div 24 - GCD(Qm,l-1) where sb := Floor(2*Sqrt(l))>;
    end if;
end function;

function skm11p(k,l)
    return k le 2 select 0 else -ZZ!(2*&+[ZZ|Gpk(k,s2,l)*H12(4*l-s2) where s2:=s*s : s in [1..sb]] + Gpk(k,0,l)*H12(4*l)) div 24 - 1 where sb := Floor(2*Sqrt(l));
end function;

function sz1(k,m,l)
    return &+[ZZ|skm1(k,mm,l):mm in Divisors(m)|IsSquarefree(m div mm)];
end function;

function newsz1(k,m,l)
    return &+[ZZ|alpha(m div mm)*skm1(k,mm,l):mm in Divisors(m)];
end function;


hf := func<d,f|&+[MoebiusMu(e)*KroneckerSymbol(d,e)*SumOfDivisors(f div e):e in Divisors(f)]>;

HH := func<n,D|IsDivisibleBy(m,a*b) select (ZZ!(a2b*KroneckerSymbol(N,(n div (a2b)))*hf(d,f))
               where f := ZZ!Sqrt(N div d) where N := (D div (a*b)^2)) else 0 where a2b := a^2*b where b,a:=SquareFree(GCD(n,D)) where m := ZZ!Sqrt(D div d) where d := FundamentalDiscriminant(D)>;

// TODO: currently broken
function newersz1p(k,N,p)
    assert IsEven(k) and k ge 2;
    if p eq 2 then return newtomo2(k,N); end if;
    if p eq 3 then return newtomo3(k,N); end if;
    if N mod p eq 0 then return newtomobadp(k,N,p); end if;
    assert IsSquarefree(N);
    mu := MoebiusMu; kron := KroneckerSymbol;
    g := k eq 2 select func<t|1> else func<t|(Vector(ZZ,[1,t^2-p])*Matrix(ZZ,2,[0,-p^2,1,t^2-2*p])^(k div 2 - 2))[2]>;
    b := Floor(2*Sqrt(p));
    if N eq 1 then return (k eq 2 select p+1 else 0) + (-(2*&+[g(t)*H12(4*p-t^2) : t in [1..b]] + g(0)*H12(4*p)) div 24) - 1; end if;
    HM := func<M,D|b*KroneckerSymbol(d,M div b)*H12(-d) where d := ExactQuotient(D,b^2) where b:=GCD(M,D)>;
    t0 := g(0)*ClassNumber(p mod 4 eq 1 select -4*p else -p)*nutl(0,p,N) div 2;
    h6 := func<d|(6 div w)*ClassNumber(d) where  w := d lt -4 select 1 else (d lt -3 select 2 else 3)>;
    sfnutl:=func<d,m,N|&+[ZZ|mu(N div (M*c))*c*kron(d,M)*&+[mu(e)*kron(d,e)*SumOfDivisors(f div e):e in Divisors(f)] where f:=m div c:M in Divisors(N div GCD(N,d*m^2)),c in Divisors(GCD(N,m))] where bad := &*[ZZ|p:p in PrimeDivisors(d)|m mod p ne 0]>;
    tpos := &+[g(t)*h6(d)*sfnutl(d,m,N) where m := ZZ!Sqrt(D div d) where d := FundamentalDiscriminant(D) where D:=t^2-4*p : t in [1..b]] div 6; 
    tpos := &+[g(t)*h6(d)*&*[ZZ|mu(N div M)*HH(M,D):M in Divisors(N)] where d:=FundamentalDiscriminant(D) where D:=t^2-4*p: t in [1..b]] div 6;
    return (k eq 2 select mu(N)*(p+1) else 0) - t0 - tpos;
end function;

function newsz1p(k,m)
    dm := Divisors(m); am := [ZZ|alpha(m div mm):mm in dm];
    skpp := [skm1p(k,mm):mm in dm];
    return func<l|&+[ZZ|am[i]*skpp[i](l):i in [1..#dm]]>;
end function;

// Here we correct the formula in [SZ], which is missing a factor of mu(n/(n,m')), as pointed out by Eran Assaf.
mu := MoebiusMu;
function cuspsz(k,m,l,n)
    return &+[ZZ|mu(n div GCD(n,mm))*skm(k,mm,l,GCD(n,mm)):mm in Divisors(m)|IsSquarefree(m div mm)];
end function;

function cuspsz1(k,m,l)
    return &+[ZZ|mu(m div mm)^2*skm1(k,mm,l):mm in Divisors(m)];
end function;

function cuspszN(k,m,l)
    return &+[ZZ|mu(m div mm)*skm(k,mm,l,mm):mm in Divisors(m)|IsSquarefree(m div mm)];
end function;

Sp := func<p,d,l|l mod p eq 0 select q+(1-KroneckerSymbol(d,p))*(q-1) div (p-1) else 1 where q := p^Valuation(l,p)>;


function Spmin(p,e,t,n,d,l) // t^2-4n = l^2d with d fundamental, n prime, s=0<e
    g := Valuation(t^2-4*n,p);
    if p ne n then
        if p eq 2 then
            a := (1-KroneckerSymbol(d,2))*Ceiling(2^(e-3));
            if e eq 1 then return -a; end if;
            if e eq 2 then return g eq 0 select a/2 else -a; end if;
            if g gt e then return -3*a; end if;
            return g eq e or g eq e-1 select (2*(-1)^d-1)*e else 0;
        else
            if g lt e-2 then return 0; end if;
            if e ne 1 and KroneckerSymbol(n,p) ne 1 then return 0; end if;
            return (1-KroneckerSymbol(d,p))*p^(e-3)/GCD(e,2) * ((e gt 2 select 1 else 0) + p*((e eq 2 select 1 else 0)
                                                                                              +(e mod 2 eq 0 and g eq e-2 select 1 else 0)
                                                                                              -(g ge e-1 select p else 0)));
        end if;
    else
        return g gt 0 select KroneckerSymbol(d,p)-1 else 0;
    end if;
end function;

function childmin(k,N,n) // Theorem 2.1 of https://arxiv.org/abs/2101.05663 for the case chi=1 and n is prime, so s=0
    if IsOdd(k) or N mod n^2 eq 0 then return 0; end if;
    Q := Factorization(N); b := Floor(2*Sqrt(n));
    C2 := ExactQuotient(&+[ZZ|Gpk(k,t,n)*H12(-d)*&*[ZZ|Sp(p,d,l):p in PrimeDivisors(l)]*&*[QQ|Spmin(q[1],q[2],t,n,d,l):q in Q]
          where l:=ZZ!Sqrt(D div d) where d:=FundamentalDiscriminant(D) where D:=t^2-4*n : t in [-b..b]],24);
    if #Q eq 1 and Q[1][1] eq 2 and IsEven(Q[1][2]) and Q[1][2] gt 2 and n ne 2 then
        gamma := Valuation(n-1,2); ee := Q[1][2] div 2 -1;
        C3 := gamma ge ee select 2^(Q[1][2] div 2)*(n+1) div 8 * (1 - (gamma eq ee select 2 else 0)) else 0;
    else C3 := N eq 1 select 1 else 0; end if;
    C4 := k eq 2 select MoebiusMu(N)*(N mod n eq 0 select 1 else (n+1)) else 0;
    print C2,C3,C4;
    return -C2-C3+C4; // C1 = 0 because n is prime
end function;

intrinsic ALNewDims(N::RngIntElt,k::RngIntElt) -> SeqEnum[RngIntElt], RngIntElt, RngIntElt
{ Returns a list of dimensions of the Atkin-Lehner subspaces of S^new_k(N), followed by the dimension of the plus and minus spaces of the Fricke involution.
  List is lex-sorted on sign signatures, e.g. +++,++-,+-+,...,---, where the nth sign corresponds to the nth smallest prime divisor of N.
  The plus/minus space is the sum of dimensions for sign signatures with even/odd number of - signs. }
    require N ge 1: "The level N must be positive";
    require k ge 2 and IsEven(k): "The weight k must be a positive even integer.";
    A := Factorization(N); w := #A; n := 2^w;
    C := CartesianPower([0,1],w);
    b := Vector(Rationals(),[newsz(k,N,1,&*[Integers()|A[i][1]^A[i][2]:i in [1..w]|c[i] eq 1]):c in C]);
    M := Matrix(Rationals(),[[&*[Integers()|-1:i in [1..w]|ci[i] eq 1 and cj[i] eq 1]:ci in C]:cj in C]);
    s := [Integers()|v[i]:i in [1..n]] where v:=b*M^-1;
    return s, Integers()!((b[1]+b[n])/2), Integers()!((b[1]-b[n])/2);
end intrinsic;

intrinsic FrickeNewDims(N::RngIntElt,k::RngIntElt) -> RngIntElt, RngIntElt
{ Returns the dimensions of the plus and minus spaces of S^new_k(N) under the Fricke involution. }
    require N ge 1: "The level N must be positive";
    require k ge 2 and IsEven(k): "The weight k must be a positive even integer.";    
    a := newtomo1(k,N); b := newpopaN1(k,N);
    return ExactQuotient(a+b,2), ExactQuotient(a-b,2);
end intrinsic;

intrinsic CuspTrace(N::RngIntElt,k::RngIntElt,n::RngIntElt) -> RngIntElt
{ Trace of T(n) on S_k(N). }
    require N ge 1: "The level N must be positive";
    require k ge 2 and IsEven(k): "The weight k must be a positive even integer.";
    require n ge 1: "n must be a positive integer";
    return GCD(N,n) eq 1 select sz1(k,N,n) else popa1(k,N,n);
end intrinsic;

intrinsic CuspTrace1(k::RngIntElt,p::RngIntElt) -> RngIntElt
{ Trace of T(p) on S_k(1). }
    require k ge 2 and IsEven(k): "The weight k must be a positive even integer.";
    if k le 10 then return 0; end if;
    require IsPrime(p): "p must be prime";
    return skm11p(k,p);
end intrinsic;

intrinsic NewTrace(N::RngIntElt,k::RngIntElt,n::RngIntElt) -> RngIntElt
{ Trace of T(n) on S_k^new(N). }
    require N ge 1: "The level N must be positive";
    require k ge 2 and IsEven(k): "The weight k must be a positive even integer.";
    require n ge 1: "n must be a positive integer";
    return GCD(N,n) eq 1 select newsz1(k,N,n) else newpopa1(k,N,n);
end intrinsic;

intrinsic NewTraces(N::RngIntElt,k::RngIntElt,n::RngIntElt) -> SeqEnum[RngIntElt]
{ Trace of T(p) on S_k^new(N) for primes p <= n. }
    require N ge 1: "The level N must be positive";
    require k ge 2 and IsEven(k): "The weight k must be a positive even integer.";
    f := newsz1p(k,N);
    return [N mod p eq 0 select newpopa1(k,N,p) else f(p):p in PrimesInInterval(1,n)];
end intrinsic;

intrinsic FrickeCuspTrace(N::RngIntElt,k::RngIntElt,n::RngIntElt) -> RngIntElt
{ Trace of T(n)*W(N) on S_k(N). }
    require N ge 1: "The level N must be positive";
    require k ge 2 and IsEven(k): "The weight k must be a positive even integer.";
    require n ge 1: "n must be a positive integer";
    return popaN(k,N,n);
end intrinsic;

intrinsic FrickeNewTrace(N::RngIntElt,k::RngIntElt,n::RngIntElt) -> RngIntElt
{ Trace of T(n)*W(N) on S_k^new(N) for n = 1 or prime. }
    require N ge 1: "The level N must be positive";
    require k ge 2 and IsEven(k): "The weight k must be a positive even integer.";
    if n eq 1 then return newpopaN1(k,N); end if;
    if IsPrime(n) then return newpopaNp(k,N,n); end if;
    require GCD(N,n) eq 1: "Currently only n=1, n prime, and n coprime to N are supported.";
    return newsz(k,N,n,N);
end intrinsic;

intrinsic FrickeNewTraces(N::RngIntElt,k::RngIntElt,n::RngIntElt) -> SeqEnum[RngIntElt]
{ Trace of T(n)*W(N) on S_k^new(N) for n = 1 or prime. }
    require N ge 1: "The level N must be positive";
    require k ge 2 and IsEven(k): "The weight k must be a positive even integer.";
    f := newpopaNp(k,N);
    return [f(p):p in PrimesInInterval(1,n)];
end intrinsic;

intrinsic ALNewTrace(N::RngIntElt,k::RngIntElt,n::RngIntElt,Q::RngIntElt) -> RngIntElt
{ Trace of T(n)*W(Q) on S_k^new(N) for n coprime to N and Q dividing N coprime to N/Q. }
    require N ge 1: "The level N must be positive";
    require k ge 2 and IsEven(k): "The weight k must be a positive even integer.";
    require n ge 1 and GCD(N,n) eq 1: "n must be a positive integer coprime to N";
    require Q ge 1 and IsDivisibleBy(N,Q) and GCD(Q, N div Q) eq 1: "Q must be a positive divisor of N coprime to N/Q";
    return newsz(k,N,n,Q);
end intrinsic;

intrinsic ALNewTraces(N::RngIntElt,k::RngIntElt,nmax::RngIntElt,Q::RngIntElt:PrimesOnly:=true) -> SeqEnum[RngIntElt]
{ Trace of T(n)*W(Q) on S_k^new(N) for n <= nmax coprime to N and Q dividing N coprime to N/Q. Restricts to n prime by default. }
    require N ge 1: "The level N must be positive";
    require k ge 2 and IsEven(k): "The weight k must be a positive even integer.";
    require Q ge 1 and IsDivisibleBy(N,Q) and GCD(Q, N div Q) eq 1: "Q must be a positive divisor of N coprime to N/Q";
    if PrimesOnly then
        newszpp := newszp(k,N,Q);
        return [newszpp(p) : p in PrimesInInterval(1,nmax)|N mod p ne 0];
    else
        return [newsz(k,N,n,Q):n in PrimesInInterval(1,nmax)|N mod n ne 0];
    end if;
end intrinsic;

intrinsic QDimensionCuspForms (N::RngIntElt,k::RngIntElt) -> RngIntElt
{ The Q-dimension of the new subspace of cuspdial forms of weight k for Gamma0(N). }
    return tomo1(k,N); // this is 100x faster than using the more general formulas above
end intrinsic;

intrinsic QDimensionNewCuspForms (N::RngIntElt,k::RngIntElt) -> RngIntElt
{ The Q-dimension of the new subspace of cuspdial forms of weight k for Gamma0(N). }
    return newtomo1(k,N); // this is 100x faster than using the more general formulas above
end intrinsic;

// One can do better than this for trivial character, N square free, and when cond(chi) is a proper divisor of N, see Stein 9.19,9.21,9.22,
// but this bound (due to Buzzard) works for all spaces M_k(N,chi) and is best possible in some cases, see Stein 9.20
intrinsic SturmBound (N::RngIntElt, k::RngIntElt) -> RngIntElt
{ Sturm bound for space of modular forms of level N weight k and any character. }
    require N ge 1 and k ge 1: "Level N and weight k must be positive integers";
    m := Index(Gamma0(N));
    return Integers()!Floor(k*m/12);
end intrinsic;

intrinsic TraceForm (N::RngIntElt, k::RngIntElt, n::RngIntElt) -> SeqEnum[RngIntElt]
{ List of the first n coefficients of the trace form for the space of modular forms of weight k for Gamma0(N). }
    return atoii(Pipe("gp -q", Sprintf("a=mfcoefs(mftraceform([%o,%o]),%o); print(a[2..%o])",N,k,n,n+1)));
end intrinsic;
