// We want to solve tau(p^4)= kappa \cdot q^b
// Here kappa is odd, and q is an odd prime not dividing 5 kappa.

sieve:=function(kappa,q);
	assert IsPrime(q);
	assert IsOdd(q);
	assert IsOdd(kappa);
	assert Valuation(5*kappa,q) eq 0;
    assert Valuation(kappa,5) in [0,1];
    if IsDivisibleBy(kappa,5) then
	    rad := &*PrimeDivisors(AbsoluteValue(kappa div 5));
        levels:=[2^3*5^2*rad*q];
    else
	    rad := &*PrimeDivisors(AbsoluteValue(kappa));
        levels:=[2^3*5*rad*q];
    end if;
    bads:=[* *];
	for level in levels do
    	NFs:=Newforms(CuspForms(level));
   		// print "There are", #NFs, "conjugacy classes of newforms at level", level;
		// print "with factorization", Factorisation(level);
    	for i in [1..#NFs] do
            f:=NFs[i,1];
            // print "Dealing with", i, "-th newform";
            K:=NumberField(Parent(Coefficient(f,1)));
            // print "Coefficient field is", K;
            if Degree(K) eq 1 then
                // print "corresponding to elliptic curve", EllipticCurve(f);
		        // print CremonaReference(EllipticCurve(f));
            end if;
            L:=PrimesInInterval(3,700);
            Exclude(~L,17);
            Exclude(~L,5);
            Exclude(~L,q);
            L:=[l : l in L | l in PrimeDivisors(kappa) eq false];
            M:=1224;
            L:=[l : l in L | IsDivisibleBy(M,Order(GF(l)!q))];
            // print L;
            if Valuation(level,q) eq 0 then
	            D:=[b: b in [0..(M-1)] | IsDivisibleBy(b,17) eq true];
            else
	            D:=[b: b in [0..(M-1)] | IsDivisibleBy(b,17) eq false];
            end if;
            D:=[b : b in D | kappa*(Integers(4)!q)^b eq 1];
            D1:=D;
            D3:=D;
	        for l in L do
	    	    if l in [3,5,7,11,13] eq false then
		    	    prs:={ < s,t > : t,s in GF(l) | s*(t^4-3*s^17*t^2+s^34) ne 0 };
                elif l eq 3 then
                    prs:={<s,s+1> : s in GF(l)};
                elif l eq 5 then
                    prs:={<s,s^2*(s+1)> : s in GF(l)};
                elif l eq 7 then
                    prs:={<s,s*(s^3+1)> : s in GF(l)};
                elif l eq 11 then
                    prs:={<s,s*(s^5+1)> : s in GF(l)};
                elif l eq 13 then
                    prs:={<s,s*(s^3+1)> : s in GF(l)};
                end if;
		        prs:={pr : pr in prs | pr[1] ne 0};
		        prs:={pr : pr in prs | pr[2]^4-3*pr[2]^2*pr[1]^17+pr[1]^34 ne 0};
		        Cl1:=[];
                Cl3:=[];
		        for pr in prs do
                    s,t:=Explode(pr);
                    a2:=3*s^17-2*t^2;
                    a4:=t^4-3*s^17*t^2+s^34;
			        E1:=EllipticCurve([0,a2,0,a4,0]);      // p = 1 mod 4
			        E3:=EllipticCurve([0,-a2,0,a4,0]);     // p = 3 mod 4
				    if IsDivisibleBy(Integers()!(Norm(Trace(E3)-Coefficient(f,l))),17) then
				        Include(~Cl3,a4);
			        end if;
				    if IsDivisibleBy(Integers()!(Norm(Trace(E1)-Coefficient(f,l))),17) then
				        Include(~Cl1,a4);
			        end if;
                end for;
                //print l,Cl1,Cl3;
		        D3:=[b : b in D3 | kappa*(GF(l)!q)^b in Cl3];
		        D1:=[b : b in D1 | kappa*(GF(l)!q)^b in Cl1];
		        // print l,D1,D3;
                if #D1 eq 0 and #D3 eq 0 then
                    break;
                end if;
	        end for;
            if #D1 ne 0 or #D3 ne 0 then
                if Degree(K) eq 1 then
                    bads:=bads cat [* [* kappa, q, level , D1, D3, K, aInvariants(EllipticCurve(f)) *] *];
                else
                    bads:=bads cat [* [* kappa, q, level , D1, D3, K, f *] *];
                end if;
            end if;
        end for;
    end for;
    return bads;
end function;

bads:=[* *];
for q in PrimesInInterval(3,100) do
    if q ne 5 and KroneckerSymbol(5,q) eq 1 then
        print "q=", q;
        bads:=bads cat sieve(1,q);
        bads:=bads cat sieve(-1,q);
        bads;
        print "++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++";
    end if;
end for;