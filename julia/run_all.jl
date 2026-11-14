include("DumontCore.jl"); using .DumontCore
checks = 0
function ok(cond, msg)
    global checks
    cond || error("FAILED: " * msg)
    checks += 1
end
oddsubsets(N) = (odds = collect(3:2:N); [Set(odds[[(m >> (k-1)) & 1 == 1 for k in 1:length(odds)]]) for m in 0:(1<<length(odds))-1])
# 1. Theorem 2.1 against the permanent, every R, N <= 13
for N in 1:2:13, R in oddsubsets(N)
    ok(transfer(N, R) == permcount(N, R), "transfer N=$N R=$R")
end
println(stdout, "Theorem 2.1 (transfer) checked: ", checks)
# 2. Theorem A closed form, n <= 7 against permanent, n <= 40 against transfer
for n in 1:7, j in 0:n
    ok(a_closed(n, j) == permcount(2n - 1, Rj(n, j)), "closed n=$n j=$j")
end
for n in 1:40, j in 0:n
    ok(a_closed(n, j) == transfer(2n - 1, Rj(n, j)), "closed/transfer n=$n j=$j")
end
# recurrence (ii)
for n in 1:30, j in 0:n
    ok(a_closed(n + 1, j + 1) == a_closed(n + 1, j) - (n - j) * (n - j + 1) * a_closed(n, j), "rec n=$n j=$j")
end
println(stdout, "Theorem A (sizes) checked: ", checks)
# 3. Theorem B against first-letter permanents, every R, N <= 13
for N in 1:2:13, R in oddsubsets(N)
    ok(firstrec(N, R) == firstcounts(N, R), "firstrec N=$N R=$R")
end
println(stdout, "Theorem B (first letters) checked: ", checks)
# 4. Corollaries for the family D_{2n-1,j}, n <= 6
for n in 2:6, j in 1:n
    b = firstcounts(2n - 1, Rj(n, j)); f = n - j
    for r in 1:2*f
        ok(b[r] == cld(r, 2) * a_closed(n - 1, j), "lower zone n=$n j=$j r=$r")
    end
    ok(b[2n-1] == 0, "last letter n=$n j=$j")
    ok(b[2n-2] == a_closed(n - 1, j - 1) && b[2n-3] == a_closed(n - 1, j - 1), "top pair n=$n j=$j")
    if j >= 2 && f >= 1
        cf1 = f * a_closed(n - 1, j) + a_closed(n - 1, j - 1) - 2 * f^2 * a_closed(n - 2, j - 1)
        ok(b[2*f+1] == cf1 && b[2*f+2] == cf1, "first upper pair n=$n j=$j")
    end
end
println(stdout, "Corollary 4.1 checked: ", checks)
# 5. Theorem C against acyclic orientations, every graph on n <= 4 vertices
for n in 1:4
    pairs = [(a, b) for a in 1:n for b in a+1:n]
    for m in 0:(1<<length(pairs))-1
        E = [pairs[k] for k in 1:length(pairs) if (m >> (k-1)) & 1 == 1]
        ok(-chi_stable(n, E, -1) == acyclic_orientations(n, E), "regions n=$n E=$E")
    end
end
println(stdout, "Theorem C (regions) checked: ", checks)
# 6. Proposition 5.1 path model against Theorem C, n <= 7
for n in 1:7
    for m in 0:(1<<n)-1
        S = Set(k for k in 1:n if (m >> (k-1)) & 1 == 1)
        E = [(a, b) for a in S for b in S if a < b]
        for t in -3:4
            ok(chi_clique_path(n, S, t) == chi_stable(n, E, t), "path n=$n S=$S t=$t")
        end
    end
end
# moving max S to any larger vertex leaves chi unchanged, n <= 7
for n in 1:7, m in 0:(1<<n)-1
    S = Set(k for k in 1:n if (m >> (k-1)) & 1 == 1)
    length(S) >= 1 || continue
    M = maximum(S); u = length(S) >= 2 ? maximum(setdiff(S, [M])) : 0
    for w in u+1:n
        S2 = union(setdiff(S, [M]), [w])
        for t in -3:4
            ok(chi_clique_path(n, S2, t) == chi_clique_path(n, S, t), "maxS move n=$n S=$S w=$w t=$t")
        end
    end
end
# 7. regions of clique on last m vertices = a(n, n-m)
for n in 1:9, m in 0:n
    S = Set((n - m + 1):n)
    j = n - m
    ok(-chi_clique_path(n, S, -1) == a_closed(n, j), "regions clique n=$n m=$m")
end
println(stdout, "Proposition 5.1 checked: ", checks)
# 8. cycle distribution of D_{2n-1,j} (Corollary), brute force n <= 5
function cyclepoly_brute(N, R)
    A = [allowed(N, R, i) for i in 1:N]
    P = zeros(BigInt, N + 1)
    function rec(i, used, s)
        if i > N
            seen = falses(N); c = 0
            for a in 1:N
                if !seen[a]
                    c += 1; b = a
                    while !seen[b]; seen[b] = true; b = s[b]; end
                end
            end
            P[c+1] += 1; return
        end
        for v in A[i]
            used[v] && continue
            used[v] = true; s[i] = v; rec(i + 1, used, s); used[v] = false
        end
    end
    rec(1, falses(N), zeros(Int, N))
    return P
end
function cyclepoly_formula(n, S)
    P = zeros(BigInt, 2n)
    for p in DumontCore.setpartitions(collect(1:n))
        any(count(v -> v in S, b) > 1 for b in p) && continue
        k = length(p)
        poly = [BigInt(1)]                       # coefficients in x, ascending
        mul!(c) = (q = zeros(BigInt, length(poly) + 1); for (i, a) in enumerate(poly); q[i] += a * c; q[i+1] += a; end; poly = q)
        for i in 0:k-1; mul!(i); end             # rising factorial x(x+1)...(x+k-1)
        for j in 1:n-1
            top = Set((n - j + 1):n)
            mul!(count(b -> any(x in top for x in b), p))
        end
        sgn = iseven(n - k) ? 1 : -1
        for (i, a) in enumerate(poly); P[i] += sgn * a; end
    end
    return P
end
for n in 1:5, m in 0:n
    N = 2n - 1
    b = cyclepoly_brute(N, Rj(n, n - m))
    f = cyclepoly_formula(n, Set((n - m + 1):n))
    ok(b == f[1:length(b)] && all(iszero, f[length(b)+1:end]), "cycles n=$n m=$m")
end
println(stdout, "Corollary 5.3 checked: ", checks)
flush(stdout); println(stdout, "ALL CHECKS PASSED: ", checks)
