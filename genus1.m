freeze;
/*
    Dependencies: utils.m
    Various utility functions for working with genus 1 curves, including elliptic curves, mostly over Q and over finite fields).

    Copyright (c) Andrew V. Sutherland, 2019-2025.  See License file for details on copying and usage.
*/

minimal := func<a,b|&and[Valuation(b,r[1]) lt 6:r in F|r[2] ge 4] where F:=Factorization(GCD(a,b))>;
havemodpoly := func<n|n le 60>;

declare attributes RngInt: ModularPolynomialCache;

function loadmodpoly(filename)
    R<X,Y> := PolynomialRing(Integers(),2);
    S := [Split(r," "): r in Split(Read(filename))];
    S := [<[atoi(c[1]),atoi(c[2])] where c:=Split(r[1][2..#r[1]-1],","),atoi(r[2])>:r in S];
    return &+[r[2]*X^r[1][1]*Y^r[1][2]:r in S|r[1][1] eq r[1][2]] +
           &+[r[2]*(X^r[1][1]*Y^r[1][2]+X^r[1][2]*Y^r[1][1]):r in S|r[1][1] ne r[1][2]];
end function;

intrinsic ModularPolynomial(N::RngIntElt:filename:=Sprintf("phi_j_%o.txt",N)) -> RngMPol
{ The modular polynomial Phi_N (this function will dynamically load and cache polynomials that ClassicalModularPolynomial does not know if they are available in phi_j_N.txt, which you can download from https://math.mit.edu/~drew/ClassicalModPolys.html for N <= 400 and prime N < 1000. }
    R<X,Y> := PolynomialRing(Integers(),2);
    try return ClassicalModularPolynomial(N); catch e; end try;
    ZZ := Integers();
    if not assigned ZZ`ModularPolynomialCache then ZZ`ModularPolynomialCache:= []; end if;
    if IsDefined(ZZ`ModularPolynomialCache,N) then return ZZ`ModularPolynomialCache[N]; end if;
    ZZ`ModularPolynomialCache[N] := loadmodpoly(filename);
    return ZZ`ModularPolynomialCache[N];
end intrinsic;

intrinsic LMFDBLabel(E::CrvEll[FldRat]) -> MonStgElt
{ Given an elliptic curve E/Q with conductor within the extent of CremonaDatabase (currently this means < 500000), returns the LMFDB label of the curve (not particularly fast but it works). }
    D := CremonaDatabase();
    E := MinimalModel(E);
    N,i,n := CremonaReferenceData(D,E);
    S := [e: e in EllipticCurves(D,N) | n eq 1 where _,_,n:=CremonaReferenceData(D,e)];
    LS := [LSeries(e) : e in S]; m := NumberOfIsogenyClasses(D,N);
    B := 8; repeat B *:= 2; T := [[Integers()|an:an in LGetCoefficients(L,B)]: L in LS]; until #Set(T) eq m;
    T := Sort(T);
    j := Index(T,[Integers()|an: an in LGetCoefficients(LSeries(E),B)]); assert j gt 0;
    k := Index(Sort([Coefficients(e):e in EllipticCurves(D,N,i)]),Coefficients(E)); assert k gt 0;
    return Sprintf("%o.%o%o",N,Base26Encode(j-1),k);
end intrinsic;

intrinsic LMFDBLabel(CremonaLabel::MonStgElt) -> MonStgElt
{ Returns the LMFDB label of the elliptic curve E/Q with the specified Cremona label. }
    return LMFDBLabel(EllipticCurve(CremonaLabel));
end intrinsic;

intrinsic EllipticCurvesOfConductorDividing(N::RngIntElt) -> SeqEnum[CrvEll]
{ Returns a list of elliptic curves over Q whose conductor divides N. }
    return &cat[[E:E in EllipticCurves(D,M)|n eq 1 where _,_,n := CremonaReferenceData(D,E)]:M in Divisors(N)] where D:=CremonaDatabase();
end intrinsic;

intrinsic EllipticCurvesOfNaiveHeightBoundedBy (H::RngIntElt) -> SeqEnum[SeqEnum[RngIntElt]]
{ List of all pairs of integers [a,b] such that y^2 = x^3 + ax + b is the minimal short Weierstrass model of an elliptic curve over Q with naive height max(4|a|^3,27*b^2) <= H.  The corresponding elliptic curves are unique representatives of their Q-isomorphism class. }
    Amax := Floor((H/4)^(1/3));
    Bmax := Floor((H/27)^(1/2));
    As := [-Amax..Amax]; Bs := [-Bmax..Bmax];
    return [[a,b]:a in As, b in Bs|4*a^3+27*b^2 ne 0 and minimal(a,b)];
end intrinsic;

intrinsic MinimalShortWeierstrassModel(E::CrvEll[FldRat]) -> CrvEll[FldRat]
{ Given an elliptic curve E/Q returns an elliptic curve in short Weierstrass form y^2 = x^3 + Ax + B with A and B minmal (no prime p with p^4|A and p^6|B). }
    E := WeierstrassModel(MinimalModel(IntegralModel(E)));
    a := Coefficients(E); assert a[1] eq 0 and a[2] eq 0 and a[3] eq 0;
    A := Integers()!a[4]; B:=Integers()!a[5];
    P := PrimeDivisors(GCD(A,B));
    for p in P do while Valuation(A,p) ge 4 and Valuation(B,p) ge 6 do A div:= p^4; B div:= p^6; end while; end for;
    return EllipticCurve([0,0,0,A,B]);
end intrinsic;

intrinsic NaiveHeight(E::CrvEll[FldRat]) -> RngIntElt
{ Given an elliptic curve E/Q returns the naive height max(4|A|^3,27*B^2), where A and B are the integer coefficients of a minimal short Weierstrass model y^2 = x^3 + Ax + B for E. }
    a := Coefficients(MinimalShortWeierstrassModel(E));
    return Max(4*Abs(a[4])^3,27*a[5]^2);
end intrinsic;

intrinsic PrimitiveDivisionPolynomial (E::CrvEll, n::RngIntElt) -> RngUPolElt
{ The divisor of the n-division polynomial whose roots are the x-coordinates of kbar-points of order n on E/k. }
    f := DivisionPolynomial(E,n);
    if IsPrime(n) then return f; end if;
    for p in PrimeDivisors(n) do f := ExactQuotient(f,GCD(f,DivisionPolynomial(E,ExactQuotient(n,p)))); end for;
    return f;
end intrinsic;

intrinsic PrimitiveDivisionPolynomial2 (E::CrvEll, n::RngIntElt) -> RngUPolElt
{ The primitive division polynomial of the j-invariant 1728 curve E with x^2 replaced by x. }
    require jInvariant(E) eq 1728: "E must have jInvariant 1728";
    f := PrimitiveDivisionPolynomial(E,n);
    return Parent(f)![Coefficient(f,m):m in [0..Degree(f)]|IsEven(m)];
end intrinsic;

intrinsic PrimitiveDivisionPolynomial3 (E::CrvEll, n::RngIntElt) -> RngUPolElt
{ The primitive division polynomial of the j-invariant 0 curve E with x^3 replaced by x. }
    require jInvariant(E) eq 0: "E must have jInvariant 0";
    f := PrimitiveDivisionPolynomial(E,n);
    return Parent(f)![Coefficient(f,m):m in [0..Degree(f)]|m mod 3 eq 0];
end intrinsic;

intrinsic IsogenyOrbits (E::CrvEll, n::RngIntElt) -> RngIntElt
{ The multiset of sizes of Galois orbits of cyclic isogenies of degree n. }
    if n eq 1 then return 1; end if;
    require havemodpoly(n): Sprintf("modular polynomial not available for n = %o", n);
    R<x> := PolynomialRing(BaseRing(E));
    return {* Degree(a[1])^^a[2] :a in Factorization(Evaluate(ModularPolynomial(n),[jInvariant(E),x])) *};
end intrinsic;

intrinsic IsogenyDegree (E::CrvEll, n::RngIntElt) -> RngIntElt
{ The minimal degree of an extension over which E has a rational cyclic isogeny of degree n. }
    if n eq 1 then return 1; end if;
    require havemodpoly(n): Sprintf("modular polynomial not available for n = %o", n);
    R<x> := PolynomialRing(BaseRing(E));
    m := Min([Degree(a[1]):a in Factorization(Evaluate(ModularPolynomial(n),[jInvariant(E),x]))]);
    return m;
end intrinsic;

intrinsic IsogenyGaloisGroup (E::CrvEll, n::RngIntElt) -> RngIntElt
{ The Galois group of the minimal extension over which all cyclic n-isogenies from E are defined. }
    if n eq 1 then return CyclicGroup(1); end if;
    require havemodpoly(n): Sprintf("ClassicalModularPolynomial not available for n = %o",n);
    R<x> := PolynomialRing(BaseRing(E));
    return GaloisGroup(Evaluate(ModularPolynomial(n),[jInvariant(E),x]));
end intrinsic;

intrinsic KummerOrbits (E::CrvEll, n::RngIntElt) -> RngIntElt
{ The multiset of sizes of Galois orbits of E[n] for an elliptic curve E. }
    require n gt 0: "n must be positive.";
    if n eq 1 then return 1; end if;
    A := Factorization(PrimitiveDivisionPolynomial(E,n));
    return {* Degree(a[1])^^a[2] : a in A *};
end intrinsic;

// functions for testing whether f is a square mod g, where f and g are polynomials over some ring.
// Used by TorsionOrbits
function sqmodtest(f,g,n)
    // check squareness modulo a bunch of small primes coprime to n (square testing in char zero is expensive)
    K := BaseRing(g);  if K eq Rationals() then K := RationalsAsNumberField(); end if;
    c := 0;
    for p in PrimesInInterval(K,1,n) do
        F,phi := ResidueClassField(p); R := PolynomialRing(F);
        if phi(n) eq 0 then continue; end if;
        fp := ChangeRing(f,phi); gp := ChangeRing(g,phi);
        if Degree(GCD(fp,Derivative(fp))) gt 1 or Degree(GCD(gp,Derivative(gp))) gt 1 then continue; end if;
        A := Factorization(gp);
        if #[a:a in A|not IsSquare(quo<R|a[1]>!fp)] gt 0 then return false; end if;
        c +:= 1;
        if c gt 10 then break; end if;
    end for;
    return true;
end function;

function ssqmod(f,g,n) // tests whether f is a square in K[x]/(g) or not
    if not sqmodtest(f,g,n) then return false; end if;
    return IsSquare(quo<PolynomialRing(BaseRing(g))|g>!f);
end function;

function fsqmod(f,g,n)
    if not sqmodtest(f,g,n) then return false; end if;
    R<x> := PolynomialRing(BaseRing(f));
    R<X,Y> := PolynomialRing(BaseRing(f),2);
    B := Factorization(Resultant(Y^2-Evaluate(f,X),Evaluate(g,X),X));
    if #B eq 1 and B[1][2] eq 1 then return false; end if;
    // if resultant of h is square free then f is a square mod g precisely when h = (-1)^deg(x)*u(x)u(-x) for some u
    if &and[a[2] eq 1:a in B] then
        S:= [Evaluate(a[1],[0,x]):a in B];
        if &and[(-1)^Degree(g)*Evaluate(g,-x) ne g:g in S] then
            return &and[(-1)^Degree(g)*Evaluate(g,-x) in S:g in S];
        end if;
    end if;
    return ssqmod(f,g,n);
end function;

intrinsic TorsionOrbits (E::CrvEll, n::RngIntElt:slow:=false) -> RngIntElt
{ The multiset of sizes of Galois orbits of E[n] for an elliptic curve E. }
    require n gt 0: "n must be positive.";
    if n eq 1 then return 1; end if;
    E := WeierstrassModel(E);  f := HyperellipticPolynomials(E);
    psi := PrimitiveDivisionPolynomial(E,n);
    A := Factorization(psi);
    // if n is odd and the primitive n-division polynomial is irreducible, so is primitive torsion polynomial
    if #A eq 1 and A[1][2] eq 1 and IsOdd(n) then return {* 2*Degree(A[1][1]) *}; end if;
    if n eq 2 then return {* Degree(a[1])^^a[2] : a in A *}; end if;
    return slow select {* ssqmod(f,a[1],n) select Degree(a[1])^^(2*a[2]) else (2*Degree(a[1]))^^a[2] : a in A *}
                  else {* fsqmod(f,a[1],n) select Degree(a[1])^^(2*a[2]) else (2*Degree(a[1]))^^a[2] : a in A *};
end intrinsic;

intrinsic TorsionDegree (E::CrvEll, n::RngIntElt:slow:=false) -> RngIntElt
{ The minimal degree of an extension over which E has a rational point of order n. }
    require n gt 0: "n must be positive.";
    if n eq 1 then return 1; end if;
    E := WeierstrassModel(E);  f := HyperellipticPolynomials(E);
    A := Factorization(PrimitiveDivisionPolynomial(E,n));
    // if n is odd and the primitive n-division polynomial is irreducible, so is primitive torsion polynomial
    if #A eq 1 and A[1][2] eq 1 and IsOdd(n) then return 2*Degree(A[1][1]); end if;
    d := Min([Degree(a[1]):a in A]);
    return slow select Min([(ssqmod(f,a[1],n) select 1 else 2)*Degree(a[1]) : a in A | Degree(a[1]) lt 2*d])
                  else Min([(fsqmod(f,a[1],n) select 1 else 2)*Degree(a[1]) : a in A | Degree(a[1]) lt 2*d]);
end intrinsic;

intrinsic PrimitiveTorsionPolynomial (E::CrvEll, n::RngIntElt) -> RngIntElt
{ Polynomial whose splitting field is the n-torsion field of E. }
    require n gt 0: "n must be positive.";
    if n eq 1 then return 1; end if;
    E := WeierstrassModel(E);  f := HyperellipticPolynomials(E);
    if n eq 2 then return f; end if;
    R<X,Y> := PolynomialRing(BaseRing(f),2);
    g := PrimitiveDivisionPolynomial(E,n);               // roots of g are all x-coords of points of order n
    h := Resultant(Y^2-Evaluate(f,X),Evaluate(g,X),X);   // roots of h are all y-coords of points of order n
    return Evaluate(h,[0,Parent(g).1])*g;
end intrinsic;

intrinsic TorsionGaloisGroup (E::CrvEll, n::RngIntElt) -> RngIntElt
{ Galois group of the n-torsion field of E (this can be extremely expensive, use with caution). }
    return GaloisGroup(PrimitiveTorsionPolynomial(E,n));
end intrinsic;

intrinsic FullTorsionDegree (E::CrvEll, n::RngIntElt) -> RngIntElt
{ The degree of the n-torsion field of E. }
    return #TorsionGaloisGroup(E,n);
end intrinsic;

intrinsic TorsionField (E::CrvEll, n::RngIntElt) -> RngIntElt
{ The n-torsion field of E/K, where K is a number field (this can be extremely expensive, use with caution). }
    K,_ := SplittingField(PrimitiveTorsionPolynomial(E,n));
    return K;
end intrinsic;

function IsHCPRoot(D,j)  // returns true if j is a root of H_D(x), attempts to use Weber polys when possible
    if D mod 8 eq 5 then return Evaluate(HilbertClassPolynomial(D),j) eq 0; end if;
    F := Parent(j);
    H,f := WeberClassPolynomial(D);
    return Degree(GCD(ChangeRing(Denominator(f),F)*j - ChangeRing(Numerator(f),F), ChangeRing(H,F))) gt 0;
end function;

/* The function below is a test harness for FrobeniusMatrix, use Test(q,func<x|FrobeniusMatrix(E)>) to test it on every elliptic curve E/Fq
function Test(q,f)
    sts := true;
    for j in GF(q) do
        E := EllipticCurveFromjInvariant(j);
        for e in Twists(E) do
            A:=f(e);
            if Trace(A) ne Trace(e) then printf "Trace mismatch %o != %o for elliptic curve E=%o over F_%o with j(E)=%o\n", Trace(A), Trace(e), Coefficients(e), q, jInvariant(e); sts:= false; end if;
            if Determinant(A) ne q then printf "Determinant mismatch %o != %o for elliptic curve E=%o over F_%o with j(E)=%o\n", Determinant(A), q, Coefficients(e), q, jInvariant(e); sts:= false; end if;
            D := A[1][2] eq 0 select 1 else (4*A[2][1]+A[1][1]-A[2][2]) div A[1][2];
            if D eq 1 then
                assert Trace(A)^2 eq 4*q;
            else
                if not IsHCPRoot(D,j) then printf "Endomorphism ring mismatch D=%o is incorrect for elliptic curve E=%o over F_%o with j(E)=%o and trace t=%o\n", D, Coefficients(e), q, jInvariant(e), TraceOfFrobenius(e); sts:= false; end if;
            end if;
        end for;
    end for;
    return sts;
end function;
*/

/* Based on Lemma 25 of David Kohel's thesis, complexity is O(M(ell^2*log(q))*log(q)) but slower in the range of interest than using Atkin modular polynomials so not currently used
function OnFloorKohel(E,t,v,D0,ell)
    if v mod ell ne 0 then return true; end if;
    if ell eq 2 then return #TwoTorsionSubgroup(E) lt 4; end if;
    a := D0 mod 4 eq 1 select (t+v) div 2 else t div 2;
    a := a mod ell;
    assert a ne 0;
    psi := DivisionPolynomial(E,ell);
    R<x> := quo<PolynomialRing(BaseRing(E))|psi>;
    if IsEven(a) then a := ell-a; end if; // for convenience
    psia := R!DivisionPolynomial(E,a);
    phia := (x*psia^2 - (R!f1)*(R!f2)*R!F) where _,f1,F := DivisionPolynomial(E,a-1) where _,f2 := DivisionPolynomial(E,a+1);
    q := #BaseRing(E);
    return (x^q*psia^2-phia) ne 0;
end function;
*/

function OnFloor(E,ell)
    if ell eq 2 then return #TwoTorsionSubgroup(E) lt 4; end if;
    return NumberOfRoots(Evaluate(AtkinModularPolynomial(ell),[PolynomialRing(BaseRing(E)).1,jInvariant(E)])) le ell;
end function;

function HeightAboveFloor(E,ell,h)
    // assumes j(E) != 0,1728 and E is ordinary
    if h eq 0 then return 0; end if;
    s := OnFloor(E,ell) select 0 else 1;
    if h le 1 or s eq 0 then return s; end if;
    j := jInvariant(E);
    R<x> := PolynomialRing(Parent(j));
    R2<X,Y> := PolynomialRing(Parent(j),2);
    phi := Evaluate(ModularPolynomial(ell),[X,Y]);
    j1 := Roots(Evaluate(phi,[j,x]));
    if #j1 ne ell+1 then return h; end if; // double roots can only happen at the surface
    if #j1 lt 3 then return 0; end if;
    j0 := [j,j,j]; j1 := [j1[i][1]:i in [1..3]];
    h := 1;
    while true do
        for i:=1 to 3 do
            r := Roots(ExactQuotient(Evaluate(phi,[j1[i],x]),x-j0[i]));
            if #r eq 0 then return h; end if;
            j0[i] := j1[i];  j1[i] := r[1][1];
        end for;
        h +:= 1;
    end while;
end function;

// returns j0, d where j0 is j-invariant on surface above j and d is the distance from j to j0
function ClimbToSurface(j,ell,h)
    if h eq 0 then return j, 0; end if;
    if j eq 0 or j eq 1728 then return j,0; end if;
    R<x> := PolynomialRing(Parent(j));
    R2<X,Y> := PolynomialRing(Parent(j),2);
    phi := Evaluate(ModularPolynomial(ell),[X,Y]);
    jj := Roots(Evaluate(phi,[j,x]));
    if &or[r[2] gt 1 : r in jj] or j in {r[1]:r in jj} then return j, 0; end if; // double roots can only happen at the surface
    if h eq 1 then if #jj eq 1 then return jj[1][1], 1; else return j, 0; end if; end if;
    jj := [r[1] : r in jj]; j0 := [j : r in jj]; j1 := jj;
    e := 0; i := 1;
    while #j1 gt 1 do
        e +:= 1;
        j2 := [[r[1] : r in Roots(ExactQuotient(Evaluate(phi,[j1[i],x]),x-j0[i]))] : i in [1..ell+1]];
        if [] in j2 then
            ii := [n : n in [1..#j2] | j2[n] ne []];
            if #ii eq 0 then return j, 0; end if; // if we hit the floor simultaneously on every path we must have started on the surface
            i := ii[1]; break;
        end if;
        j0 := j1; j1 := [r[1] : r in j2];
    end while;
    if e eq h then return j, 0; end if;
    xj := j; j := jj[i]; d := 1; e +:= 1; // e is height of j above floor
    function walk(phi,nj,xj,n)
        for i:=1 to n do r := Roots(ExactQuotient(Evaluate(phi,[nj,x]),x-xj)); if #r eq 0 then return false; end if; xj:=nj; nj:=r[1][1]; end for;
        return true;
    end function;
    while e lt h do
        assert j ne 0 and j ne 1728;
        nj := [r[1]:r in Roots(ExactQuotient(Evaluate(phi,[j,x]),x-xj))];  assert #nj eq ell;
        i := 1; while i le ell and not walk(phi,nj[i],j,e+1) do i +:= 1; end while;
        xj := j; j := nj[i]; d +:= 1; e +:= 1;
    end while;
    return j,d;
end function;

intrinsic PrecomputeEndomorphismRingData(B::RngIntElt) -> Assoc
{ Returns an associative array of precomputed Frobenius matrices for elliptic curves y^2=x^3+Ax+B over Fp with B square and j!=0,1728 for 3 < p < B (one twist for each j!=0,1728). }
    Z := [[]:i in [1..B]];
    for p in PrimesInInterval(5,B) do
        Z[p] := [[Integers()|]:i in [1..p]];
        for j in GF(p) do
            r := PrimitiveRoot(p);
            if j ne 0 and j ne 1728 then
                A := 3*j*(1728-j);  B := 2*j*(1728-j)^2;
                if not IsSquare(B) then A *:= r^2; B *:= r^3; end if;
                a,b,D := EndomorphismRingData(EllipticCurve([A,B]));
                Z[p][Integers()!j] := [a,b,D];
            end if;
        end for;
    end for;
    return Z;
end intrinsic;

intrinsic EndomorphismRingData(E::CrvEll[FldFin]) -> RngIntElt, RngIntElt, RngIntElt
{ Given an elliptic curve E/Fq returns integers a, b, D, with 4*q=a^2-b^2*D, where a is the trace of the Frobenius endomorphism pi, D is the discriminant of the ring End(E) cap Q(pi). }
    q := #BaseRing(E);  _,p,e := IsPrimePower(q);
    j := jInvariant(E);
    a := TraceOfFrobenius(E);
    if j eq 0 and p ne 2 then
        D := [-4*p,-4,a^2 eq 4*q select 1 else -3,0,0,1][#AutomorphismGroup(E) div 2];
        b := D eq 1 select 0 else (bb where _,bb := IsSquare((a^2 - 4*q) div D));
        return a, b, D;
    elif j eq 1728 then
        D := [#TwoTorsionSubgroup(E) eq 4 select -p else -4*p,a^2 eq 4*q select 1 else -4,-3,0,0,0,0,0,0,0,0,1][#AutomorphismGroup(E) div 2];
        b := D eq 1 select 0 else (bb where _,bb := IsSquare((a^2 - 4*q) div D));
        return a, b, D;
    elif a mod p eq 0 then
        r2 := #TwoTorsionSubgroup(E) eq 4;
        D := a^2 eq 4*q select 1 else (r2 select -p else -4*p);
        b := D eq 1 select 0 else (r2 select 2 else 1)*p^((e-1) div 2);
        return a, b, D;
    end if;
    // If we get here E is ordinary and j(E) != 0,1728 
    D := a^2 - 4*q;  D0 := FundamentalDiscriminant(D); _,v := IsSquare(D div D0);
    if v eq 1 then return a,1,D; end if;
    if IsPrime(v) then
       if v gt 400 or v*v gt 8*Abs(D0) then
            if IsHCPRoot(D0,j) then return a,v,D0; else return a, 1, D; end if;
        else
            if OnFloor(E,v) then return a, 1, D; else return a, v, D0; end if;
        end if;
    end if;
    L := Factorization(v);
    if &and[ell[2] le 1 : ell in L | ell[1] gt 60] and L[#L][1] lt 400 and (#L eq 1 or L[#L][1] lt 4*Abs(D) div L[#L][1]^2) then
        b := &*[ell[1]^HeightAboveFloor(E,ell[1],ell[2]) : ell in L];
        return a, b, D div (b*b);
    end if;
    u := 1; w := v;
    for ell in L do if ell[1] lt 60 then j,d := ClimbToSurface(j,ell[1],ell[2]); u *:= ell[1]^d; w div:=ell[1]^ell[2]; end if; end for;
    for uu in Prune(Divisors(w)) do if IsHCPRoot(uu^2*D0,j) then return a, (v div (u*uu)), uu^2*u^2*D0; end if; end for;
    return a, (v div (u*w)), u^2*w^2*D0;
end intrinsic;

intrinsic EndomorphismRingData(E::CrvEll[FldRat], q::RngIntElt) -> RngIntElt, RngIntElt, RngIntElt
{ Given an elliptic curve E/Fq returns integers a, b, D, with 4*q=a^2-b^2*D, where a is the trace of the Frobenius endomorphism pi, D is the discriminant of the ring End(E) cap Q(pi). }
    return EndomorphismRingData(ChangeRing(E,GF(q)));
end intrinsic;

intrinsic FrobeniusMatrix(E::CrvEll[FldFin]) -> AlgMatElt[RngInt]
{ Given an elliptic curve E/Fq returns a 2-by-2 integer matrix whose reduction modulo any integer N coprime to q gives the action of Frobenius on E[N] with respect to some basis. }
    a, b, D := EndomorphismRingData(E);
    return Matrix([[(a+b*d) div 2, b], [b*(D-d) div 4, (a-b*d) div 2]]) where d := D mod 2;
end intrinsic;

intrinsic FrobeniusMatrices(E::CrvEll[FldRat], B::RngIntElt:B0:=1) -> SeqEnum[AlgMatElt[RngInt]]
{ Given an elliptic curve E/Q and a bound B returns a list of 2-by-2 integer matrices A of determinant p (for primes p <= B of good reduction) whose reduction modulo any integer N coprime to det(A) gives the action of Frobenius on (E mod p)[N] with respect to some basis. }
    E := MinimalModel(E); D := Integers()!Discriminant(E);
    return [FrobeniusMatrix(ChangeRing(E,GF(p))) : p in PrimesInInterval(B0,B) | D mod p ne 0];
end intrinsic;

intrinsic FrobeniusMatrices(E::CrvEll[FldNum], B::RngIntElt:B0:=1) -> SeqEnum[AlgMatElt[RngInt]]
{ Given an elliptic curve E/Q and a bound B returns a list of 2-by-2 integer matrices A of determinant p (for primes p <= B of good reduction) whose reduction modulo any integer N coprime to det(A) gives the action of Frobenius on (E mod p)[N] with respect to some basis. }
    K := BaseRing(E); D := RingOfIntegers(BaseRing(E))!Discriminant(E);
    return [FrobeniusMatrix(Reduction(E,p)) : p in PrimesInInterval(K,B0,B:coprime_to:=D)];
end intrinsic;

// copy of GL2SimilarityInvariant in gl2base.m, we do this to make genus1.m independent of gl2base.m
function SimilarityInvariant(M)
    isscalar := func<M|M[1][1] eq M[2][2] and M[1][2] eq 0 and M[2][1] eq 0>;
    N := #BaseRing(M);
    Z := Integers();
    S := [];
    for a in Factorization(N) do
        p := a[1]; e := a[2];
        A := ChangeRing(M,Integers(p^e));
        j := Max([0] cat [j:j in [1..e] | isscalar(ChangeRing(A,Integers(p^j)))]);
        if j eq 0 then S cat:= [[Z|0,0,Determinant(A),Trace(A)]]; continue; end if;
        if j eq e then S cat:= [[Z|e,A[1][1],0,0]]; continue; end if;
        q := p^j; r := p^(e-j);
        A := ChangeRing(A,Integers());
        z := A[1][1] mod q;
        S cat:= [[Z|j,z,ExactQuotient((A[1][1]-z)*(A[2][2]-z)-A[1][2]*A[2][1],q*q) mod r,ExactQuotient(Trace(A)-2*z,q) mod r]];
    end for;
    return S;
end function;

/*
  The precomputed lists Xn below contain sets of similarity-invariants of elements of GL(2,Integers(n)) that do not appear in maximal subgroups with det-index 1
  Computed by code in gl2base.m using
  for n in [8,9,5,7,13] do
    G := SL(2,Integers(n)); S := GL2SimilaritySet(G);
    X := [S diff GL2SimilaritySet(H`subgroup) : H in MaximalSubgroups(G) | GL2DeterminantIndex(H`subgroup) eq EulerPhi(n)];
    printf "X%o := %o;\n", n,sprint(X);
  end for;
*/
X8 := [{[[0,0,1,6]],[[1,1,2,0]],[[1,1,0,0]],[[1,1,3,2]],[[0,0,1,2]],[[1,1,1,2]]},{[[0,0,1,1]],[[0,0,1,7]],[[0,0,1,5]],[[0,0,1,3]]},{[[0,0,1,6]],[[0,0,1,4]],[[0,0,1,2]],[[0,0,1,0]]}];
X9 := [{[[0,0,1,4]],[[1,2,2,1]],[[0,0,1,5]],[[1,1,2,0]],[[1,2,1,1]],[[1,2,0,1]],[[0,0,1,2]],[[1,1,0,0]],[[0,0,1,3]],[[1,1,1,0]],[[0,0,1,6]],[[0,0,1,7]]},{[[0,0,1,6]],[[0,0,1,3]],[[0,0,1,0]]},{[[0,0,1,1]],[[0,0,1,8]],[[0,0,1,7]],[[0,0,1,4]],[[0,0,1,5]],[[0,0,1,2]]}];
X5 := [{[[0,0,1,2]],[[0,0,1,3]]},{[[0,0,1,1]],[[0,0,1,4]]},{[[0,0,1,2]],[[0,0,1,3]]}];
X7 := [{[[0,0,1,4]],[[0,0,1,3]],[[0,0,1,0]]},{[[0,0,1,5]],[[0,0,1,2]]},{[[0,0,1,5]],[[0,0,1,2]]}];
X13 := [{[[0,0,1,4]],[[0,0,1,5]],[[0,0,1,10]],[[0,0,1,11]],[[0,0,1,8]],[[0,0,1,9]],[[0,0,1,2]],[[0,0,1,3]],[[0,0,1,6]],[[0,0,1,7]]},{[[0,0,1,10]],[[0,0,1,11]],[[0,0,1,6]],[[0,0,1,8]],[[0,0,1,7]],[[0,0,1,5]],[[0,0,1,2]],[[0,0,1,3]]},{[[0,0,1,1]],[[0,0,1,11]],[[0,0,1,4]],[[0,0,1,9]],[[0,0,1,12]],[[0,0,1,2]]},{[[0,0,1,10]],[[0,0,1,6]],[[0,0,1,8]],[[0,0,1,7]],[[0,0,1,5]],[[0,0,1,3]]}];

// This function implements an augmented version of Zywina's ExceptionalPrimes algorithm in https://arxiv.org/abs/1508.07661
intrinsic PossiblyNonsurjectivePrimes(E::CrvEll[FldRat]:A:=[],B:=256,Fast:=false) -> SeqEnum
{ Given an elliptic curve E/Q, returns a list of primes ell for which the ell-adic representation attached to E could be non-surjective. This list provably contains all such primes and usually contains no others. }
    require BaseRing(E) eq Rationals()and not HasComplexMultiplication(E): "E must be a non-CM elliptic curve over Q";
    E := MinimalModel(E); D := Integers()!Discriminant(E);
    j := jInvariant(E); den := Denominator(j);
    S := {2,3,5,7,13};
    if j in {-11^2,-11*131^3} then Include(~S,11); end if;
    if j in {-297756989/2, -882216989/131072} then Include(~S,17); end if;
    if j in {-9317, -162677523113838677} then Include(~S,37); end if;
    if den ne 1 then
        ispow,b,e:=IsPower(den);
        if ispow then
            P := {p : p in PrimeDivisors(e) | p ge 11};
            if P ne {} then                
                S join:= {l : l in PrimeDivisors(g) | l ge 11} where g := GCD({&*P} join {p^2-1 : p in PrimeDivisors(b)});
            end if;
        end if;
    else
        Q := PrimeDivisors(GCD(Numerator(j-1728),Numerator(D)*Denominator(D)));
        Q := [q: q in Q | q ne 2 and IsOdd(Valuation(j-1728,q))];
        if Valuation(j,2) in {3,6,9} then Q cat:= [2]; end if;
        p:=2; alpha:=[]; beta:=[];
        repeat
            a:=0;
            while a eq 0 do
                p:=NextPrime(p); K:=KodairaSymbol(E,p);
                a := K eq KodairaSymbol("I0") select TraceOfFrobenius(E,p) else (K eq KodairaSymbol("I0*") select TraceOfFrobenius(QuadraticTwist(E,p),p) else 0);
            end while;
            S join:= {l : l in PrimeDivisors(a) | l gt 13};
            alpha cat:= [[(1-KroneckerSymbol(q,p)) div 2 : q in Q]];  beta cat:= [[(1-KroneckerSymbol(-1,p)) div 2]];
            M := Matrix(GF(2),alpha); b:=Matrix(GF(2),beta);
        until IsConsistent(Transpose(M),Transpose(b)) eq false;
    end if;
    if Fast then return Sort([l:l in S]); end if;
    if #A eq 0 then A := FrobeniusMatrices(E,B); end if;
    n := #[s:s in X8|#(t meet s) eq 0] where t:={SimilarityInvariant((GL(2,Integers(8))!a)^Order(Integers(8)!Determinant(a))):a in A|Determinant(a) ne 2};
    if n eq 0 then Exclude(~S,2); end if;
    n := #[s:s in X9|#(t meet s) eq 0] where t:={SimilarityInvariant((GL(2,Integers(9))!a)^Order(Integers(9)!Determinant(a))):a in A|Determinant(a) ne 3};
    if n eq 0 then Exclude(~S,3); end if;
    n := #[s:s in X5|#(t meet s) eq 0] where t:={SimilarityInvariant((GL(2,Integers(5))!a)^Order(Integers(5)!Determinant(a))):a in A|Determinant(a) ne 5};
    if n eq 0 then Exclude(~S,5); end if;
    n := #[s:s in X7|#(t meet s) eq 0] where t:={SimilarityInvariant((GL(2,Integers(7))!a)^Order(Integers(7)!Determinant(a))):a in A|Determinant(a) ne 7};
    if n eq 0 then Exclude(~S,7); end if;
    n := #[s:s in X13|#(t meet s) eq 0] where t:={SimilarityInvariant((GL(2,Integers(13))!a)^Order(Integers(13)!Determinant(a))):a in A|Determinant(a) ne 13};
    if n eq 0 then Exclude(~S,13); end if;
    S := Sort([l:l in S]);
    return S;
end intrinsic;

intrinsic PossiblyNonsurjectivePrimes(E::CrvEll[FldNum]:A:=[],B:=1024) -> SeqEnum
{ Given an elliptic curve E over a number field K, returns a list of primes ell <= B for which the ell-adic representation attached to E could be non-surjective (the ell-adic representation could be surjective for some of these primes and could be non-surjective at some primes > B).  Based on Algorithm 6 in https://arxiv.org/abs/1504.07618. }
    require not HasComplexMultiplication(E): "E must be non-CM";
    require B ge 7: "B must be at least 7";
    if #A eq 0 then A := GL2FrobeniusMatrices(E,256); end if;
    S := {l : l in PrimesInInterval(11,B)}; X := [0:i in [1..B]];
    for a in A do
        t := Trace(a); d := Determinant(a);
        c := t^2 - 4*d; r := t^2/d;
        T := [];
        for l in S do
            if IsDivisibleBy(d,l) then continue; end if;
            x := KroneckerSymbol(c,l); if x eq 0 then continue; end if;
            X[l] := BitwiseOr(X[l],x eq 1 select 1 else 2);
            if X[l] eq 7 then Append(~T,l); continue; end if;
            u := Integers(l)!r;
            if u ne 1 and u ne 2 and u ne 4 and (3-u)*u ne 1 then
                X[l] := BitwiseOr(X[l],4);
                if X[l] eq 7 then Append(~T,l); end if;
            end if;
        end for;
        S diff:= Set(T);
    end for;
    n := #[s:s in X8|#(t meet s) eq 0] where t:={GL2SimilarityInvariant((GL(2,Integers(8))!a)^Order(Integers(8)!Determinant(a))):a in A|not IsEven(Determinant(a))};
    if n gt 0 then Include(~S,2); end if;
    n := #[s:s in X9|#(t meet s) eq 0] where t:={GL2SimilarityInvariant((GL(2,Integers(9))!a)^Order(Integers(9)!Determinant(a))):a in A|not IsDivisibleBy(Determinant(a),3)};
    if n gt 0 then Include(~S,3); end if;
    n := #[s:s in X5|#(t meet s) eq 0] where t:={GL2SimilarityInvariant((GL(2,Integers(5))!a)^Order(Integers(5)!Determinant(a))):a in A|not IsDivisibleBy(Determinant(a),5)};
    if n gt 0 then Include(~S,5); end if;
    n := #[s:s in X7|#(t meet s) eq 0] where t:={GL2SimilarityInvariant((GL(2,Integers(7))!a)^Order(Integers(7)!Determinant(a))):a in A|not IsDivisibleBy(Determinant(a),7)};
    if n gt 0 then Include(~S,7); end if;
    S := Sort([l:l in S]);
    return S;
end intrinsic;
