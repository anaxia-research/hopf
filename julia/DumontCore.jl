# Core definitions shared by the verification programs.
module DumontCore
export allowed, permcount, firstcounts, transfer, Gpoly_eval, a_closed, Rj, firstrec, chi_stable, chi_clique_path, acyclic_orientations

# Allowed values at position i for R-D-permutations of [N]
function allowed(N, R, i)
    if iseven(i)
        return collect(1:i)
    elseif i in R || i == 1
        return collect(1:N)
    else
        return collect(i:N)
    end
end

# Independent count: permanent by bitmask dynamic programming (row by row)
function permcount(N, R; first::Int=0)
    A = [allowed(N, R, i) for i in 1:N]
    if first > 0
        A[1] = first in A[1] ? [first] : Int[]
    end
    dp = Dict{UInt32,BigInt}(UInt32(0) => BigInt(1))
    for i in 1:N
        nd = Dict{UInt32,BigInt}()
        for (m, c) in dp, v in A[i]
            b = UInt32(1) << (v - 1)
            if m & b == 0
                nd[m|b] = get(nd, m | b, BigInt(0)) + c
            end
        end
        dp = nd
    end
    return get(dp, UInt32((1 << N) - 1), BigInt(0))
end

firstcounts(N, R) = [permcount(N, R; first=r) for r in 1:N]

# Theorem 2.1: one-dimensional transfer with weights U, L, F
function transfer(N, R)
    st = Dict{Int,BigInt}(0 => BigInt(1))
    for t in N:-1:1
        nd = Dict{Int,BigInt}()
        add!(h, w) = (h >= 0 && (nd[h] = get(nd, h, BigInt(0)) + w))
        for (h, w) in st
            if iseven(t)
                add!(h, w * (h + 1)); add!(h + 1, w)
            elseif t in R || t == 1
                add!(h - 1, w * h * h); add!(h, w * (2h + 1)); add!(h + 1, w)
            else
                add!(h - 1, w * h * h); add!(h, w * (h + 1))
            end
        end
        st = nd
    end
    return get(st, 0, BigInt(0))
end

Rj(n, j) = Set(1:2:(2 * (n - j) - 1))

# G_j evaluated at x via the operator recurrence G_{j+1}(x) = (x+1)[(x+2)G_j(x+1) - x G_j(x)]
const Gmemo = Dict{Tuple{Int,Int},BigInt}()
function Gpoly_eval(j, x)
    j == 1 && return BigInt(1)
    get!(Gmemo, (j, x)) do
        (x + 1) * ((x + 2) * Gpoly_eval(j - 1, x + 1) - x * Gpoly_eval(j - 1, x))
    end
end
function a_closed(n, j)
    j == 0 && return factorial(big(n))^2
    f = n - j
    return factorial(big(f)) * factorial(big(f + 1)) * Gpoly_eval(j, f)
end

# Theorem B: first-letter recurrence for arbitrary R
const memo = Dict{Tuple{Int,Vector{Int}},Vector{BigInt}}()
function firstrec(N, R)
    key = (N, sort(collect(R)))
    haskey(memo, key) && return memo[key]
    if N == 1
        return [BigInt(1)]
    end
    b = zeros(BigInt, N)
    R0 = Set(x - 2 for x in R if x >= 3)
    b[1] = sum(firstrec(N - 2, R0))
    for k in 1:div(N - 1, 2)
        b[2k] = b[2k-1]
        Rp = Set(vcat([x for x in R if x <= 2k - 1], [x - 2 for x in R if x >= 2k + 3]))
        bp = firstrec(N - 2, Rp)
        if (2k + 1) in R
            b[2k+1] = b[2k] + sum(bp)
        else
            b[2k+1] = b[2k] + sum(bp[2k:end]) - sum(bp[1:2k-1])
        end
    end
    memo[key] = b
    return b
end

# set partitions of a vector
function setpartitions(v)
    isempty(v) && return [Vector{Vector{Int}}()]
    out = Vector{Vector{Vector{Int}}}()
    for p in setpartitions(v[2:end])
        for i in eachindex(p)
            q = deepcopy(p); pushfirst!(q[i], v[1]); push!(out, q)
        end
        q = deepcopy(p); pushfirst!(q, [v[1]]); push!(out, q)
    end
    return out
end

# Theorem C: characteristic polynomial value chi(t) of H(G), G on [n] given by edge list
function chi_stable(n, E, t)
    tot = BigInt(0)
    for p in setpartitions(collect(1:n))
        ok = all(!(any(e[1] in b && e[2] in b for b in p)) for e in E)
        ok || continue
        k = length(p)
        ff = prod(BigInt(t - i) for i in 0:k-1; init=BigInt(1))
        pr = BigInt(1)
        for j in 1:n-1
            top = Set((n - j + 1):n)
            d = count(b -> any(x in top for x in b), p)
            pr *= (t - d)
        end
        tot += ff * pr
    end
    return tot
end

# Proposition 5.1: path model for G a clique on S (G-vertex labels), others isolated
function chi_clique_path(n, S, t)
    st = Dict{Int,BigInt}(0 => BigInt(1))   # d = number of colours used
    s = 0
    for step in 1:n
        v = n - step + 1                      # vertex coloured at this step
        nd = Dict{Int,BigInt}()
        for (d, w) in st
            nd[d+1] = get(nd, d + 1, BigInt(0)) + w * (t - d)
            reuse = v in S ? d - s : d
            reuse > 0 && (nd[d] = get(nd, d, BigInt(0)) + w * reuse)
        end
        v in S && (s += 1)
        st = nd
        if step <= n - 1
            st = Dict(d => w * (t - d) for (d, w) in st)
        end
    end
    return sum(values(st); init=BigInt(0))
end

# Brute force: acyclic orientations of Gamma_G
function gammagraph(n, E)
    N = 2n - 1
    edges = Tuple{Int,Int}[]
    for (a, b) in E                        # G-vertex i -> odd 2n-2i+1
        push!(edges, (2n - 2a + 1, 2n - 2b + 1))
    end
    for i in 1:n, j in i:n-1
        push!(edges, (2i - 1, 2j))
    end
    return N, edges
end
function acyclic_orientations(n, E)
    N, edges = gammagraph(n, E)
    m = length(edges); c = 0
    for mask in 0:(1<<m)-1
        adj = [Int[] for _ in 1:N]
        for (k, (a, b)) in enumerate(edges)
            if (mask >> (k - 1)) & 1 == 1
                push!(adj[a], b)
            else
                push!(adj[b], a)
            end
        end
        indeg = zeros(Int, N)
        for u in 1:N, w in adj[u]; indeg[w] += 1; end
        q = [u for u in 1:N if indeg[u] == 0]; seen = 0
        while !isempty(q)
            u = pop!(q); seen += 1
            for w in adj[u]; indeg[w] -= 1; indeg[w] == 0 && push!(q, w); end
        end
        seen == N && (c += 1)
    end
    return c
end
end
