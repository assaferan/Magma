freeze;
/*
    Dependencies: utils.m, chars.m, genus1.m, gl2base.m

    This module implements the algorithm for counting points on modular curve X_H described in the paper

        "$\ell$-adic images of Galois for elliptic curves over $\mathbb Q$",
        by J. Rouse, D. Zureick-Brown, and A.V. Sutherland, with an appendix by J. Voight,
        Forum of Math, Sigma 10 (2022), 62 pages, available at

            https://www.cambridge.org/core/journals/forum-of-mathematics-sigma/article/ell-adic-images-of-galois-for-elliptic-curves-over-mathbb-q-and-an-appendix-with-john-voight/D5BC92F9949B387570A7D764635B6AC8

    Please be sure to cite this paper if you use this software in your research.

    Copyright (c) Andrew V. Sutherland, 2019-2025.  See License file for details on copying and usage.
*/

import "gl2base.m": gl2N1;

function GetClassNumber(htab,D) return -D le #htab select htab[-D] else ClassNumber(D); end function;

// Use Cornacchia's algorithm to solve x^2 + dy^2 = m for (x,y) with x,y > 0
function norm_equation(d,m)
    if not IsSquare(m) then
        c,a,b := NormEquation(d,m);
        if not c then return false,_,_; else return c,a,b;  end if;
    end if;
    t,r1 := IsSquare(Integers(m)!-d);
    if not t then return false,_,_; end if;
    r1 := Integers()!r1;
    if 2*r1 gt m then r1 := m-r1; end if;
    r0 := m;
    while r1^2 ge m do s := r0 mod r1; r0:= r1;  r1:= s; end while;
    t,s := IsSquare((m-r1^2) div d);
    if not t then return false,_,_; end if;
    return t,r1,s;
end function;

// Apply Theorem 2.1 of Duke and Toth, given a,b,D satisfying that 4q=a^2-b^2D, where a is the trace of the Frobenius endomorphism pi,
// D is the discriminant of Rpi := End(E) cap Q[pi], and b is the index of Z[pi] in Rpi unless Z[pi]=Z in which case D=1 and b=0
// see https://arxiv.org/abs/math/0103151
// returns a list of integers representing an element of GL_2(Z) with trace a and determinant q representing action of Frob (up to conj)
function FrobMat(a,b,D)
    // assert (b gt 0 and D lt 0 and IsDiscriminant(D)) or (b eq 0 an dD eq 1);
    return [(a+b*d) div 2, b, b*(D-d) div 4, (a-b*d) div 2] where d := D mod 2;
end function;

forward j1728FM;

// The functions j0FM and j1728FM below each return a list of quadruples <a,b,D,w> where a,b,D define a FrobeniusMatrix (with a >= 0), and w is a rational weight
// The rational points in the fiber of X_H -> X(1) above j=0 can then be computed as the weighted sum of fixpoints of FrobMat(a,b,D).
// Based on Table 6 of https://arxiv.org/pdf/2106.11141
function j0FM(q)
    _,p,e := IsPrimePower(q);
    if p eq 2 then return j1728FM(q); end if;
    if p mod 3 eq 2 then
        if IsOdd(e) then
            return [<0,p^((e-1) div 2),-4*p,1>];
        else
            return [<p^(e div 2),p^(e div 2),-3,2/3>,<2*p^(e div 2),0,1,1/3>];
        end if;
    elif p eq 3 then
        if IsOdd(e) then
            return [<0,3^((e-1) div 2),-12,1/2>, <0,2*3^((e-1) div 2),-3,1/6>, <3^((e+1) div 2),3^((e-1) div 2),-3,1/3>];
        else
            return [<0,3^(e div 2),-4,1/2>, <3^(e div 2),3^(e div 2),-3,1/3>, <2*3^(e div 2),0,1,1/6>];
        end if;
    end if;
    c,a,b := norm_equation(3,4*q);  assert c and a gt 0 and b gt 0;
    if IsOdd(a) then
        if IsEven((a+3*b) div 2) then u := Abs(a+3*b) div 2; v := Abs(a-b) div 2; else u := Abs(a-3*b) div 2; v := Abs(a+b) div 2; end if;
    else
        u := Abs(a);v := Abs(b);
    end if;
    assert u gt 0 and v gt 0 and IsEven(u) and IsEven(v) and 4*q eq u^2+3*v^2;;
    return [<u,v,-3,1/3>, <(u+3*v) div 2,Abs((u-v) div 2),-3,1/3>, <Abs((u-3*v) div 2),(u+v) div 2,-3,1/3>];
end function;

function j0PointCount(N,f,q) GL2 := GL(2,Integers(N)); return Integers()! &+[f(GL2!FrobMat(r[1],r[2],r[3]))*r[4] : r in j0FM(q)]; end function;
function j0FrobeniusMatrices(q) return Set([FrobMat(r[1],r[2],r[3]):r in j0FM(q)] cat [FrobMat(-r[1],r[2],r[3]):r in j0FM(q)|r[1] ne 0]); end function;

function j1728FM(q)
    _,p,e := IsPrimePower(q);
    if p eq 3 then return j0FM(q); end if;
    if p mod 4 eq 3 then
        if e mod 2 eq 1 then
            return [<0,p^((e-1) div 2),-4*p,1/2>,<0,2*p^((e-1) div 2),-p,1/2>];
        else
            return [<0,p^(e div 2),-4,1/2>,<2*p^(e div 2),0,1,1/2>];
        end if;
    elif p eq 2 then
        if IsOdd(e) then
            return [<0,2^((e-1) div 2),-8,1/2>,<2^((e+1) div 2),2^((e-1) div 2),-4,1/2>];
        else
            return [<0,2^(e div 2),-4,1/4>,<2^(e div 2),2^(e div 2),-3,2/3>,<2*2^(e div 2),0,1,1/12>];
        end if;
    end if;
    c,a,b := norm_equation(4,4*q);  assert c and a gt 0 and b gt 0;
    if IsOdd(b) then u := Abs(2*b); v := Abs(a div 2); else u := Abs(a); v := Abs(b); end if;
    assert u gt 0 and v gt 0 and IsEven(u) and IsEven(v) and 4*q eq u^2+4*v^2;
    return [<a,b,b eq 0 select 1 else -4,1/2>,<2*b,a div 2,-4,1/2>];
end function;

function j1728PointCount(N,f,q) GL2 := GL(2,Integers(N)); return Integers()! &+[f(GL2!FrobMat(r[1],r[2],r[3]))*r[4] : r in j1728FM(q)]; end function;
function j1728FrobeniusMatrices(q) return Set([FrobMat(r[1],r[2],r[3]):r in j1728FM(q)] cat [FrobMat(-r[1],r[2],r[3]):r in j1728FM(q)|r[1] ne 0]); end function;

/*
  Given level N, permutation character f table C indexed by conjugacy class, class map f, class number table htab for -D <= 4q, prime power q coprime to {N
  returns the number of points on X_H(Fq) above non-cuspidal j!=0,1728

  For smallish q (say q <= 8192) we could easily precompute all the Frobenius matrix, class number pairs (which do not depend on N or f)
  but the enumeration is so fast that this doesn't really save much time (maybe a 10-20 percent speedup).
*/
function jNormalPointCount(N,f,htab,q)
    b,p,e := IsPrimePower(q); assert(b);
    GL2 := GL(2,Integers(N));
    assert GCD(q,N) eq 1;
    // To count j-invariants we only consider nonnegative traces a and divide by 2 for a=0
    // We exclude j=0 and j=1278 by skipping discriminants -3 and -4 and adjusting the supersingular counts appropriately
    cnt := 0;
    for a in [1..Floor(2*Sqrt(q))] do  // iterate over positive traces not divisible by p
        if a mod p eq 0 then continue; end if; // supersingular cases handled below
        D1 := a^2-4*q; // discriminant of Z[pi] for trace a
        D0 := FundamentalDiscriminant(D1);
        _,v:=IsSquare (D1 div D0); // 4*q = a^2 - v^2*D0 with D0 fundamental
        for u in Divisors(v) do
            D := D0*u^2;  if D ge -4 then continue; end if;   // skip j=0,1728
            cnt +:= f(GL2!FrobMat(a,v div u,D))*GetClassNumber(htab,D);
        end for;
    end for;
    if p le 3 then return cnt; end if; // for p <= 3 the supersingular j-invariants are all 0=1728
    // For p > 3 the only nonnegative traces divisible by p we need to consider are 0 (when e is odd) and 2*p^(e/2) (when e is even)
    s0 := p mod 3 eq 2 select 1 else 0; s1728 := p mod 4 eq 3 select 1 else 0;
    if e mod 2 eq 1 then
        if s1728 eq 1 then
            // There are 2 Fq-isomorphism classes per j-invariant with trace 0, including j=1728 which is the unique
            // j-invariant where the endomorphism rings are different (one has disc -p the other disc -4p)
            cnt +:= f(GL2!FrobMat(0,2*p^((e-1) div 2),-p))*ExactQuotient(GetClassNumber(htab,-p)-1,2);         // -1 for j=1728, -0 for j=0
            cnt +:= f(GL2!FrobMat(0,p^((e-1) div 2),-4*p))*ExactQuotient(GetClassNumber(htab,-4*p)-1-2*s0,2);  // -1 for j=1728, -2*s0 for j=0
        else
            cnt +:= f(GL2!FrobMat(0,p^((e-1) div 2),-4*p))*ExactQuotient(GetClassNumber(htab,-4*p)-2*s0,2);    // -0 for j=1728, -2*s0 for j=0
        end if;
    else
        // There are (p+6-4*kron(-3,p)-3*kron(-4,p))/12 j-invariants of curves with trace 2*sqrt(q)
        // of which (1-kron(-3,p))/2 have j-invariant 0 and (1-kron(-4,p))/2 have j-invariant 1728
        cnt +:= f(GL2!FrobMat(2*p^(e div 2),0,1)) * ExactQuotient(p-6+2*KroneckerSymbol(-3,p)+3*KroneckerSymbol(-4,p),12);
    end if;
    return cnt;
end function;

intrinsic GL2PointCountPrecompute(N::RngIntElt,q::RngIntElt : ind:=GL2SimilarityClassIndexMap(N),c:=GL2SimilarityClassCount(N),htab:=ClassNumberTable(4*q)) -> ModTupFldElt
{ Precomputes a vector of weighted class numbers to be used for fast point-counting on modular curves of a fixed level N over a fixed finite field Fq, using parameters ind:=GL2SimilarityClassIndexMap(N) and htab:=ClassNumberTable(B) with B >= 4*q. }
    b,p,e := IsPrimePower(q);
    require b and GCD(q,N) eq 1: "q must be a prime power coprime to N";
    GL2 := GL(2,Integers(N));
    s := Vector([Rationals()|0:i in [1..c]]); // we may have non-integral weights coming from j=0,1728
    // To count j-invariants we only consider nonnegative traces a and divide by 2 for a=0
    // We exclude j=0 and j=1278 by skipping discriminants -3 and -4 and adjusting the supersingular counts appropriately
    for a in [1..Floor(2*Sqrt(q))] do  // iterate over positive traces not divisible by p
        if a mod p eq 0 then continue; end if; // supersingular cases handled below
        D1 := a^2-4*q; // discriminant of Z[pi] for trace a
        D0 := FundamentalDiscriminant(D1);
        _,v:=IsSquare (D1 div D0); // 4*q = a^2 - v^2*D0 with D0 fundamental
        for u in Divisors(v) do
            D := D0*u^2;  if D ge -4 then continue; end if;   // skip j=0,1728
            s[ind(GL2!FrobMat(a,v div u,D))] +:= GetClassNumber(htab,D);
        end for;
    end for;
    for r in j0FM(q) do s[ind(GL2!FrobMat(r[1],r[2],r[3]))] +:= r[4]; end for;
    if p le 3 then return s; end if; // for p <= 3 the supersingular j-invariants are all 0=1728
    for r in j1728FM(q) do s[ind(GL2!FrobMat(r[1],r[2],r[3]))] +:= r[4]; end for;
    // For p > 3 the only nonnegative traces divisible by p we need to consider are 0 (when e is odd) and 2*p^(e/2) (when e is even)
    s0 := p mod 3 eq 2 select 1 else 0; s1728 := p mod 4 eq 3 select 1 else 0;
    if e mod 2 eq 1 then
        if s1728 eq 1 then
            // There are 2 Fq-isomorphism classes per j-invariant with trace 0, including j=1728 which is the unique
            // j-invariant where the endomorphism rings are different (one has disc -p the other disc -4p)
            s[ind(GL2!FrobMat(0,2*p^((e-1) div 2),-p))] +:= ExactQuotient(GetClassNumber(htab,-p)-1,2);         // -1 for j=1728, -0 for j=0
            s[ind(GL2!FrobMat(0,p^((e-1) div 2),-4*p))] +:= ExactQuotient(GetClassNumber(htab,-4*p)-1-2*s0,2);  // -1 for j=1728, -2*s0 for j=0
        else
            s[ind(GL2!FrobMat(0,p^((e-1) div 2),-4*p))] +:= ExactQuotient(GetClassNumber(htab,-4*p)-2*s0,2);    // -0 for j=1728, -2*s0 for j=0
        end if;
    else
        // There are (p+6-4*kron(-3,p)-3*kron(-4,p))/12 j-invariants of curves with trace 2*sqrt(q)
        // of which (1-kron(-3,p))/2 have j-invariant 0 and (1-kron(-4,p))/2 have j-invariant 1728
        s[ind(GL2!FrobMat(2*p^(e div 2),0,1))] +:= ExactQuotient(p-6+2*KroneckerSymbol(-3,p)+3*KroneckerSymbol(-4,p),12);
    end if;
    return s;
end intrinsic;


intrinsic GL2PointCountsPrecompute(N::RngIntElt,Q::SeqEnum[RngIntElt]) -> ModMatFldElt, SeqEnum[RngIntElt]
{ Precomputes a matrix of weighted class numbers to be used for fast pointcounting on modular curves of a fixed level N modulo primes p <= B coprime to N. }
    require #[q:q in Q|GCD(N,q) ne 1] eq 0: "Q must consist of prime-powers coprime to N";
    return Transpose(Matrix([GL2PointCountPrecompute(N,q:ind:=ind,c:=c,htab:=htab):q in Q])) where ind:=GL2SimilarityClassIndexMap(N) where c:=GL2SimilarityClassCount(N) where htab:=ClassNumberTable(4*Max(Q));
end intrinsic;

intrinsic GL2PointCountsPrecompute(N::RngIntElt,B::RngIntElt) -> ModMatFldElt, SeqEnum[RngIntElt]
{ Precomputes a matrix of weighted class numbers to be used for fast pointcounting on modular curves of a fixed level N modulo primes p <= B coprime to N. }
    Q := [q:q in PrimesInInterval(1,B)|N mod q ne 0];
    return GL2PointCountsPrecompute(N,Q),Q;
end intrinsic;

intrinsic GL2PointCounts(H::GrpMat,Q::SeqEnum[RngIntElt],M::ModMatFldElt) -> SeqEnum[RngIntElt]
{ Computes vector of point counts of X_H over finite fields Fq for prime powers q in Q using precomputed matrix M (which should have a column for each q in Q). }
    require #Q eq NumberOfColumns(M): "Precomputed point-counting matrix M should have Q columns";
    N := #BaseRing(H);
    require N gt 1: "H must be defined over a ring of cardinality N > 1";
    v := Vector(Rationals(),GL2SimilarityCounts(H));
    require Degree(v) eq NumberOfRows(M): "The matrix M was not precomputed for the cardinality N of the base ring of H";
    v := Vector([Rationals()|ExactQuotient(v[i]*j,w[i]):i in [1..Degree(v)]]) where j:=GL2Index(H) where w:=GL2SimilarityCounts(N);
    v := v*M + Vector([Rationals()|C[q mod N]:q in Q]) where C:=GL2RationalCuspCounts(H) where N,H := GL2Level(H);
    return [Integers()|v[i]:i in [1..Degree(v)]];
end intrinsic;

intrinsic GL2Traces(H::GrpMat,Q::SeqEnum[RngIntElt],M::ModMatFldElt) -> SeqEnum[RngIntElt]
{ Computes vector of Frobenius traces of X_H over finite fields Fq for prime powers q in Q using precomputed matrix M (which should have a column for each q in Q). }
    t := GL2PointCounts(H,Q,M);
    return [Integers()|Q[i]+1-t[i]:i in [1..#Q]];
end intrinsic;

intrinsic GL2FrobeniusMatrices(j::FldFinElt) -> SetEnum[AlgMatElt[RngInt]]
{ The set of Frobenius matrices that arise for elliptic curves with the specified j-invariant over a finite field. }
    if j eq 0 then return j0FrobeniusMatrices(#Parent(j)); end if;
    if j eq 1728 then return j1728FrobeniusMatrices(#Parent(j)); end if;
    a, b, D := EndomorphismRingData(EllipticCurveFromjInvariant(j)); d := D mod 2;
    S := {Matrix([[(a+b*d) div 2, b], [b*(D-d) div 4, (a-b*d) div 2]])};
    return a eq 0 select S else S join {Matrix([[(-a+b*d) div 2, b], [b*(D-d) div 4, (-a-b*d) div 2]])};
end intrinsic;

intrinsic GL2FrobeniusMatrices(q::RngIntElt) -> SetEnum[AlgMatElt[RngInt]]
{ The set of Frobenius matrices that arise for elliptic curves over the field with q elements. }
    b,p,e := IsPrimePower(q); assert(b);
    S := [[r[1],r[2],r[3]]:r in j0] cat [[-r[1],r[2],r[3]]:r in j0|r[1] ne 0] where j0 := j0FM(q);
    S cat:= [[r[1],r[2],r[3]]:r in j1728] cat [[-r[1],r[2],r[3]]:r in j1728|r[1] ne 0] where j1728 := j1728FM(q);
    for a in [1..Floor(2*Sqrt(q))] do  // iterate over positive traces not divisible by p
        if a mod p eq 0 then continue; end if; // supersingular cases handled below
        D1 := a^2-4*q; // discriminant of Z[pi] for trace a
        D0 := FundamentalDiscriminant(D1);
        _,v:=IsSquare (D1 div D0); // 4*q = a^2 - v^2*D0 with D0 fundamental
        for u in Divisors(v) do
            D := D0*u^2;  if D ge -4 then continue; end if;   // skip j=0,1728
            S cat:= [[a,v div u,D], [-a,v div u,D]];
        end for;
    end for;
    // The only case where there is a supersingular Frobenius matrix not realized by j=0,1728 occurs for p=1 mod 12
    if p mod 12 eq 1 then Include(~S, e mod 2 eq 1 select [0,p^((e-1) div 2),-4*p] else [2*p^(e div 2),0,1]); end if;
    M := MatrixRing(Integers(),2);
    return {M!FrobMat(r[1],r[2],r[3]) : r in S};
end intrinsic;

intrinsic GL2FrobeniusMatrices(Fq::FldFin) -> SetEnum[AlgMatElt[RngInt]]
{ The set of Frobenius matrices that arise for elliptic curves over the finite field Fq. }
    return GL2FrobeniusMatrices(#Fq);
end intrinsic;

intrinsic GL2jCounts(H::GrpMat,q::RngIntElt:chi:=0) -> SetEnum[FldFinElt]
{ A list of counts of the number of Fq-points above each points of Y(1), ordered as GF(q) is ordered. }
    N,H := GL2Level(GL2IncludeNegativeOne(H));
    require IsPrimePower(q) and GCD(q,N) eq 1: "q must be a prime power that is coprime to the level of H";
    if N eq 1 then return [1:j in GF(q)]; end if;
    G := GL(2,Integers(N));
    f := Type(chi) eq RngIntElt select GL2PermutationCharacter(H) else chi;
    J := [];
    for j in GF(q) do
        if j eq 0 then Append(~J,j0PointCount(N,f,q)); continue; end if;
        if j eq 1728 then Append(~J,j1728PointCount(N,f,q)); continue; end if;
        Append(~J,f(G!FrobeniusMatrix(EllipticCurveFromjInvariant(j))));
    end for;
    return J;
end intrinsic;

intrinsic GL2jCounts(H::GrpMat,Q::SeqEnum[RngIntElt]) -> SeqEnum[FldFinElt]
{ A list of lists of  counts of the number of Fq-points above each points of Y(1), ordered as GF(q) is ordered for q in Q. }
    N,H := GL2Level(GL2IncludeNegativeOne(H));
    if N eq 1 then return [[1:j in GF(q)]:q in Q]; end if;
    chi := GL2PermutationCharacter(H);
    return [ GL2jCounts(H,q:chi:=chi) : q in Q ];
end intrinsic;

intrinsic GL2jInvariants(H::GrpMat,q::RngIntElt:chi:=0) -> SetEnum[FldFinElt]
{ A list of the affine points in the set j(X_H(Fq)). }
    J := GL2jCounts(H,q:chi:=chi);
    Fq := [j:j in GF(q)];
    return [Fq[i]:i in [1..q]|J[i] gt 0];
end intrinsic;

intrinsic GL2jInvariants(H::GrpMat,Q::SeqEnum) -> SeqEnum[FldFinElt]
{ A list of lists of the affine points in the set j(X_H(Fq)) for q in Q. }
    N,H := GL2Level(GL2IncludeNegativeOne(H)); if N eq 1 then return [*[j:j in GF(q)]:q in Q*]; end if;
    chi := GL2PermutationCharacter(H);
    return [* GL2jInvariants(H,q:chi:=chi) : q in Q *];
end intrinsic;

intrinsic GL2jInvariantTest(H::GrpMat,j::FldFinElt) -> BoolElt
{ True if j is an element of j(X_H(F_q)). }
    N,H := GL2Level(GL2IncludeNegativeOne(H)); if N eq 1 then return true; end if;
    G := GL(2,Integers(N));
    return &or[inv(G!A) in S:A in GL2FrobeniusMatrices(j)] where inv := GL2SimilarityClassMap(N) where S := GL2SimilaritySet(H);
end intrinsic;

intrinsic GL2jInvariantTest(H::GrpMat,j::RngIntElt,B::RngIntElt) -> BoolElt
{ True if j is an element of j(X_H(F_p)) for p <= B coprime to N. }
    N,H := GL2Level(GL2IncludeNegativeOne(H)); if N eq 1 then return true; end if;
    G := GL(2,Integers(N)); S := GL2SimilaritySet(H);
    for p in PrimesInInterval(1,B) do
        if N mod p ne 0 and not &or[inv(G!A) in S:A in GL2FrobeniusMatrices(GF(p)!j)] where inv := GL2SimilarityClassMap(N) then return false; end if;
    end for;
    return true;
end intrinsic;

intrinsic GL2jInvariantTest(H::GrpMat,j::FldRatElt,B::RngIntElt) -> BoolElt
{ True if j is an element of j(X_H(F_p)) for p <= B coprime to N and the denominator of j. }
    N,H := GL2Level(GL2IncludeNegativeOne(H)); if N eq 1 then return true; end if;
    G := GL(2,Integers(N)); S := GL2SimilaritySet(H); dj := Denominator(j);
    for p in PrimesInInterval(1,B) do
        if N mod p ne 0 and dj mod p ne 0 and not &or[inv(G!A) in S:A in GL2FrobeniusMatrices(GF(p)!j)] where inv := GL2SimilarityClassMap(N) then return false; end if;
    end for;
    return true;
end intrinsic;

// htab:=ClassNumbers(4*p), f:=GL2PermutationCharacter(H cup -H), C:=GL2RationalCuspCounts(H)
intrinsic GL2PointCount(N::RngIntElt,htab::SeqEnum[RngIntElt],f::UserProgram,C::SeqEnum[RngIntElt],q::RngIntElt) -> RngIntElt
{ Returns the number of Fq-rational points on the modular curve X_H of level N with permutation character f:=GL2PermutationCharacter(GL2IncludeNegativeOne(H)) and rational cusp counts C:=GL2RationalCuspCounts(H), given class number table htab[-D]=h(D) for discriminants |D| <= 4*q. }
    j := jNormalPointCount(N,f,htab,q); j0 := j0PointCount(N,f,q); j1728 := GCD(q,6) eq 1 select j1728PointCount(N,f,q) else 0;
    return j+j0+j1728+C[q mod N];
end intrinsic;

intrinsic GL2PointCounts(H::GrpMat,Q::SeqEnum[RngIntElt]) -> SeqEnum
{ Sequence of Fq-rational points on X_H for q in Q (which must be prime powers or lists of prime powers coprime to the level of H). }
    if #Q eq 0 then return []; end if;
    // timer := Cputime();
    lists := Type(Q[1]) eq SeqEnum;
    N,H := GL2Level(GL2IncludeNegativeOne(H));  if N eq 1 then return lists select [[q+1:q in r]:r in Q] else [q+1:q in Q]; end if;
    D := GL2DeterminantImage(H);  dindex := GL1Index(D);
    m := lists select Max([Max(r):r in Q]) else Max(Q);
    htab := #Q le 100 select ClassNumberTable(4096) else ClassNumberTable(4*m);
    C := (#Q eq 1 and not lists) select [Q[1] mod N eq i select GL2RationalCuspCount(H,Q[1]) else 0:i in [1..N]] else GL2RationalCuspCounts(H);
    f := GL2PermutationCharacter(sub<GL2Ambient(D)|H,-Identity(H)>);
    // vprintf GL2,3: "Setup for counting points at %o primes powers <= %o took %.3os\n", #Q, Max(Q), Cputime()-timer;
    pts := dindex gt 1 select func<q|GL1![q] in D select GL2PointCount(N,htab,f,C,q) else 0> else func<q|GL2PointCount(N,htab,f,C,q)> where GL1 := GL(1,Integers(N));
    P := lists select [[pts(q):q in r]:r in Q] else [pts(q):q in Q];
    // vprintf GL2,3: "Total time to count points at %o primes powers <= %o took %.3os\n", #Q, Max(Q), Cputime()-timer;
    return P;
end intrinsic;

intrinsic GL2Traces(H::GrpMat,Q::SeqEnum) -> SeqEnum
{ The Frobenius traces of X_H/Fq for q in Q (which must be prime powers or lists of prime powers coprime to the level of H). }
    if #Q eq 0 then return []; end if;
    lists := Type(Q[1]) eq SeqEnum;
    N,H := GL2Level(GL2IncludeNegativeOne(H));  if N eq 1 then return lists select [[0:q in r]:r in Q] else [0:q in Q]; end if;
    GL1 := GL(1,Integers(N));
    D := GL2DeterminantImage(H);  dindex := Index(GL1,D);
    cnts := GL2PointCounts(H,Q);
    tr := dindex gt 1 select func<q,n|GL1![q] in D select dindex*(q+1)-n else 0> else func<q,n|q+1-n>;
    return Type(Q[1]) eq SeqEnum select [[tr(Q[i][j],cnts[i][j]):j in [1..#cnts[i]]]:i in [1..#cnts]] else [tr(Q[i],cnts[i]):i in [1..#cnts]];
end intrinsic;

intrinsic GL2PointCount(H::GrpMat,q::RngIntElt) -> RngIntElt
{ The number of Fq-rational points on X_H. }
    N,H := GL2Level(GL2IncludeNegativeOne(H));
    require IsPrimePower(q) and GCD(q,N) eq 1: "q must be a prime power that is coprime to the level of H";
    return GL2PointCounts(H,[q])[1];
end intrinsic;

intrinsic GL2PointCounts(H::GrpMat,B::RngIntElt:B0:=1,PrimePowers:=false,ZeroFill:=false) -> SeqEnum
{ Sequence of Fp-point counts on X_H/Fp for p >= B0 not dividing N up to B.
  If PrimePowers is set each entry is a list of integers giving point counts over Fq for q=p,p^2,...<= B.
  If ZeroFill is set the returned array will have an entry for every prime p in [B0,B] with zeros or empty lists inserted at bad primes.
}
    N,H := GL2Level(GL2IncludeNegativeOne(H));
    Q := [p : p in PrimesInInterval(B0,B) | N mod p ne 0];
    if PrimePowers then Q := [[p^i: i in [1..Floor(Log(p,B))]] : p in Q]; end if;
    if ZeroFill then
        C := GL2PointCounts(H,Q);
        P := PrimesInInterval(B0,B); T := PrimePowers select [[Integers()|]:p in P] else [Integers()|0:p in P];
        j:=1; for i:=1 to #P do if N mod P[i] ne 0 then T[i] := C[j]; j+:=1; end if; end for;
        return T;
    else
        return GL2PointCounts(H,Q);
    end if;
end intrinsic;

intrinsic GL2Traces(H::GrpMat,B::RngIntElt:B0:=1,PrimePowers:=false,ZeroFill:=false) -> SeqEnum[RngIntElt]
{ Frobenius traces of X_H at p >= B0 (or list of traces for powers of p up to B if PrimePowers is set) not dividing N up to B.
  If ZeroFill is set the returned array will have an entry for every prime p in [B0,B] with zeros or empty lists inserted at bad primes.
}
    N,H := GL2Level(GL2IncludeNegativeOne(H));
    Q := [p : p in PrimesInInterval(B0,B) | N mod p ne 0];
    if PrimePowers then Q := [[p^i: i in [1..Floor(Log(p,B))]] : p in Q]; end if;
    if ZeroFill then
        C := GL2Traces(H,Q);
        P := PrimesInInterval(B0,B); T := PrimePowers select [[Integers()|]:p in P] else [Integers()|0:p in P];
        j:=1; for i:=1 to #P do if N mod P[i] ne 0 then T[i] := C[j]; j+:=1; end if; end for;
        return T;
    else
        return GL2Traces(H,Q);
    end if;
end intrinsic;

intrinsic GL2TraceHash(H::GrpMat) -> RngIntElt
{ Returns the trace hash of the modular curve X_H, the sum_(2^12<p<2^13) ap(p)*c_p mod 2^61-1 defined in Sec 4.3 of https://doi.org/10.1112/S146115701600019X. }
    N,H:=GL2Level(H);
    require &and[p lt 2^12 or p gt 2^13:p in PrimeDivisors(N)]: "The level of H cannot be divisible by a prime in [2^12,2^13].";
    if N lt 6 then return 0; end if;
    return TraceHash(GL2Traces(H,8192:B0:=4096));
end intrinsic;

intrinsic GL2PointCounts(H::GrpMat,p::RngIntElt,r::RngIntElt) -> SeqEnum[RngIntElt]
{ The sequence of Fq-point counts on X_H/Fq for q=p,p^2,...,p^r for a prime power p. }
    return GL2PointCounts(H,[p^i:i in [1..r]]);
end intrinsic;

intrinsic GL2Traces(H::GrpMat,p::RngIntElt,r::RngIntElt) -> SeqEnum[RngIntElt]
{ The sequence of Frobenius traces of X_H/Fq for q=p,p^2,...,p^r. }
    return GL2Traces(H,[p^i:i in [1..r]]);
end intrinsic;

intrinsic GL2LPolynomial(H::GrpMat,q::RngIntElt) -> RngUPolElt
{ The L-polynomial of X_H/Fq for a prime power q coprime to the level of H. }
    g := GL2Genus(H);
    R<T>:=PolynomialRing(Integers());
    if g eq 0 then return R!1; end if;
    return PointCountsToLPolynomial(GL2PointCounts(H,q,g),q);
end intrinsic;

intrinsic GL2IsogenyClass(H::GrpMat) -> MonStgElt, RngIntElt
{ The Cremona label of the isogeny class of the Jacobian of the genus 1 curve X_H, along with its rank.  Will fail if the level is out of range of the Cremona DB. }
    N,H := GL2Level(GL2IncludeNegativeOne(H));
    require N gt 1:  "H must be have genus 1.";
    require GL2DeterminantIndex(H) eq 1 and GL2Genus(H) eq 1: "H must have determinant index 1 and genus 1";

    P := PrimeDivisors(N);
    badi := {#PrimesUpTo(p):p in P};

    // Computes an integer M so that the conductor of any elliptic curve E/Q with good reduction outside P divides M.
    M := GCD(N^2,2^8*3^5*&*[Integers()|p^2:p in P|p gt 3]);

    D:=EllipticCurveDatabase();
    assert M lt LargestConductor(D);  // Ensures that J is isomorphic to a curve in the current database

    EE:= &cat[[EllipticCurve(D,N,i,1) : i in [1.. NumberOfIsogenyClasses(D,N)]] : N in Divisors(M)];   
    // The Jacobian of X_G is isogenous to precisely one of the curves in EE.

    function GoodTracesOfFrobenius(E,B) // Return traces up to B with traces at bad p set to p+2
        T := TracesOfFrobenius(E,B);
        return [T[i] : i in [1..#T] | not i in badi];
    end function;
  
    B := 20;  // this is already enough to distinguish all isogeny classes of prime power level <= 400000
    while #EE gt 1 do
        T := GL2Traces(H,B);
        EE:= [E: E in EE | GoodTracesOfFrobenius(E,B) eq T];
        B *:= 2;
   end while;
   assert #EE eq 1;

   // return the isogeny class label of our representative curve, along with its rank
   _,c:=Regexp("[0-9]+[a-z]+",CremonaReference(EE[1]));
   return c, Rank(EE[1]);
end intrinsic;

intrinsic GL2QInfinite(H::GrpMat:MustContainNegativeOne:=false) -> BoolElt
{ True if j(X_H(Q)) is infinite, false otherwise. }
    if not IsFinite(BaseRing(H)) then assert H eq gl2N1; return true; end if;
    if not GL2QAdmissible(H:MustContainNegativeOne:=MustContainNegativeOne) then return false; end if;
    g := GL2Genus(H);
    if g eq 0 then return true; end if;
    if g gt 1 then return false; end if;
    _,r := GL2IsogenyClass(H);
    return r gt 0;
end intrinsic;

intrinsic GL2QObstructions(H::GrpMat:g:=-1,B:=0,T:=[],C:=[]) -> SeqEnum[RngIntElt]
{ List of good places p where X_H has no Qp-points (p=0 is used for the real place). Whent specified, g:=GL2Genus(H), T:=GL2Traces(H,B), C:=GL2RationalCuspCounts(H).  B will set to NthPrime(T) if T is nonempty or to 4*g^2 if neither B nor T is specified. }
    N,H := GL2Level(GL2IncludeNegativeOne(H)); if N eq 1 then return [Integers()|]; end if;
    require GL2DeterminantIndex(H) eq 1: "H must have determinant index 1.";
    G := GL2Ambient(N); inv := GL2SimilarityClassMap(N);
    S := GL2SimilaritySet(H);
    X := [Integers()|];
    if not inv(G![1,0,0,-1]) in S and not inv(G![1,1,0,-1]) in S then Append(~X,0); end if;
    badp := Set(PrimeDivisors(N));
    if #T gt 0 then
        P := PrimesInInterval(1,NthPrime(#T));
        return X cat [P[i]:i in [1..#P]|not P[i] in badp and P[i]+1-T[i] le 0];
    end if;
    if g lt 0 then g := GL2Genus(H); end if;
    if g eq 0 then return X; end if;
    maxp := 4*g^2; if B gt 0 and B lt maxp then maxp := B; end if;
    badp := Set(PrimeDivisors(N));
    P := [p:p in PrimesInInterval(1,maxp)| not p in badp];
    if #C eq 0 then C := GL2RationalCuspCounts(H); end if;
    return X cat [p : p in P | C[p mod N] eq 0 and &and[not inv(G!a) in S : a in GL2FrobeniusMatrices(p)]]  where inv := GL2SimilarityClassMap(N);
end intrinsic;

intrinsic GL2GonalityBounds(H::GrpMat:B:=8192,ratcuspcnts:=[],ratpts:=-2,g:=-1,psl2index:=-1) -> SeqEnum[RngIntElt], RngIntElt
{ Returns a quadruple listing lower and upper bounds on the Q-gonality of X_H followed by lower and upper bounds on the Qbar-gonality (the genus > 1 the lower bounds for Q and Qbar will be the same).
  The second return value is the prime power used to prove lower bounds via point-counting (or 0 if not relevant).
  The third return value is the first prime power not checked (or 0 if none were checked); this is the least prime power for which lb*(q+1) exceeds the Weil bound q+1*2*g*sqrt(q), where lb is the lower bound on the Qbar-gonality.
  Except for special handling of genus 0,1,2 curves, this algorithm computes gonality upper bounds as the minimum of the degree of the map to X(1) and either g+1 or 2*g-1 (depending on whether rational points are known or not, for qbar they always are),
  and computes gonality lower bounds using the Abramovich-Kim-Sarnak bound gon_Qbar(X_H) >= 325*psl2index/2^15 and the bounds gon_Qbar(X_H) >= #X_H(Fq)/(q+1) for each prime power q.

}
    require GL2DeterminantIndex(H) eq 1: "H must have determinant index 1";
    N,H := GL2Level(GL2IncludeNegativeOne(H)); if N eq 1 then return [1,1,1,1], 0, 0; end if;
    if g lt 0 or psl2index lt 0 then g,gdata := GL2Genus(H); psl2index := gdata[1]; end if;
    /*
      set ratpts to 0 if we know there is an obstruction to R-points or Qp-points for some good p
      set ratpts to 1 if we know there are rational cusps or CM points, or when g=0 and level is prime power and there are no obstructions at good p (#obstructions must be even in this case)
      set ratpts to -1 otherwise
    */
    if ratpts lt -1 or ratpts gt 1 then
        ratpts := (GL2RationalCuspCount(H) gt 0 or #GL2RationalCMPoints(H) gt 0) select 1 else (not GL2ContainsComplexConjugation(H) select 0 else ((g eq 0 and IsPrimePower(N)) select 1 else -1));
    end if;
    if g eq 0 then return [ratpts eq 0 select 2 else 1,ratpts gt 0 select 1 else 2,1,1], 0, 0; end if;
    if (g eq 1 and ratpts gt 0) or g eq 2 then return [2,2,2,2], 0, 0; end if;
    lbbar := Max(2,Ceiling(325*psl2index/32768)); // Abramovich bound lower bound on C-gonality = Qbar-gonality <= Q-gonality using Kim-Sarnak bound of 975/4096 for Selberg eigenvalue bound
    ub := GL2Index(H); // degree of j-map to X(1) = P^1 is always an upper bound
    if ratpts gt 0 then ub := Min(ub,g gt 1 select g else g+1); elif g gt 1 then ub := Min(ub,2*g-2); end if;
    if lbbar eq ub then return [lbbar,ub,lbbar,ub], 0; end if;
    ubbar := Min(ub,(g+3) div 2); // See Prop A.1(v) in https://math.mit.edu/~poonen/papers/gonality.pdf
    htab := ClassNumberTable(2^16);
    C := #ratcuspcnts gt 0 select ratcuspcnts else GL2RationalCuspCounts(H);
    f := GL2PermutationCharacter(H);
    pts := func<q|GL2PointCount(N,htab,f,C,q)> where GL1 := GL(1,Integers(N));
    Q := [q:q in PrimePowers(Min(4*g*g,B))|GCD(q,N) eq 1];
    qq := 0; lq := 0;
    lb := lbbar;
    for q in Q do
        if lb*(q+1) gt q+1+2*g*Sqrt(q) then qq:=q; break; end if;
        n := pts(q);
        // #X_H(Fq) <= gon_Fq(X_H)*(q+1) for q coprime to the level since the gonal map has q+1 fibers of size <= gon_Fq(X_H)
        // this implies gon_Q(X_H) >= gon_Fq(X_H) >= #X_H(Fq)/(q+1)
        if n gt lb*(q+1) then lb := Ceiling(n/(q+1)); lq := q; end if;
    end for;
    return [lb,ub,lbbar,ubbar],lq,qq;
end intrinsic;
