using Pkg
Pkg.add(["SymPy", "Combinatorics", "Memoization", "Primes"])


using Memoization

@memoize function dimrec(a::Vector{Int}, d::Int)
    function helper(i::Int, remaining::Int)
        if i == length(a)
            return remaining == 0 ? 1 : 0
        end
        total = 0
        for k in 0:div(remaining, a[i])
            total += helper(i + 1, remaining - k * a[i])
        end
        return total
    end
    return helper(1, d)
end


using SymPy

function uniquebi(a::Int, s::Int, d::Int; verbose=false)
    b, c = symbols("b c", integer=true)
    eq = Eq(a * b + s * c, d)
    sols = diophantine(eq)
    for sol in sols
        b_val = sol[1]
        if 0 <= b_val < s
            if verbose
                println("Solution: b = $b_val, c = $(sol[2])")
            end
            return b_val
        end
    end
    error("No valid solution found for b in the specified range.")
end


function reduce_arr(func::Function, arr::Vector{Int})
    output = []
    for i in 1:length(arr)
        arrhat = vcat(arr[1:i-1], arr[i+1:end])
        push!(output, reduce(func, arrhat))
    end
    return output
end


@memoize function very_ample_bound_recursive(weights::Vector{Int})
    r = length(weights) - 1
    if r == 0
        return -weights[1]
    end
    total = 0.0
    for i in 1:length(weights)
        w_hat = vcat(weights[1:i-1], weights[i+1:end])
        total += very_ample_bound_recursive(w_hat)
    end
    m = reduce(lcm, weights)
    return (total + m) / r
end


using Combinatorics

function very_ample_bound(weights::Vector{Int})
    r = length(weights) - 1
    if r == 0
        return -weights[1]
    end
    temp_sum = 0.0
    for nu in 2:(r + 1)
        for subset in combinations(weights, nu)
            temp_sum += reduce(lcm, subset) / binomial(r - 1, nu - 2)
        end
    end
    return -sum(weights) + temp_sum / r
end


struct Weights
    weights::Vector{Int}
    reduced_weights::Vector{Int}
    wellformed_weights::Vector{Int}
    gcd::Int
    sub_gcd::Vector{Int}
    sub_lcm_of_sub_gcd::Vector{Int}
    lcm_of_sub_gcd::Int
    lcm::Int

    function Weights(weights::Vector{Int})
        sorted_weights = sort(weights)
        gcd_val = reduce(gcd, sorted_weights)
        reduced = [div(w, gcd_val) for w in sorted_weights]
        sub_gcds = reduce_arr(gcd, reduced)
        sub_lcms = reduce_arr(lcm, sub_gcds)
        wellformed = [div(r, l) for (r, l) in zip(reduced, sub_lcms)]
        lcm_sub_gcd = reduce(lcm, sub_gcds)
        lcm_val = reduce(lcm, sorted_weights)
        new(sorted_weights, reduced, wellformed, gcd_val, sub_gcds, sub_lcms, lcm_sub_gcd, lcm_val)
    end
end


struct TwistedSheaf
    W::Weights
    degree::Int
    reduced_degree::Union{Int, Nothing}
    wellformed_degree::Union{Int, Nothing}
    B::Union{Vector{Int}, Nothing}

    function TwistedSheaf(W::Weights, degree::Int)
        temp = degree / W.gcd
        if isapprox(temp, round(temp); atol=1e-10)
            reduced_deg = Int(round(temp))
            B_vals = [uniquebi(ai, si, reduced_deg) for (ai, si) in zip(W.reduced_weights, W.sub_gcd)]
            wf_deg = div(reduced_deg - sum(B_vals .* W.reduced_weights), W.lcm_of_sub_gcd)
            new(W, degree, reduced_deg, wf_deg, B_vals)
        else
            new(W, degree, nothing, nothing, nothing)
        end
    end
end


struct LinearSystem
    sheaf::TwistedSheaf
    dimension::Int

    function LinearSystem(W::Weights, degree::Int)
        sheaf = TwistedSheaf(W, degree)
        if sheaf.wellformed_degree !== nothing
            dim = dimrec(W.wellformed_weights, sheaf.wellformed_degree) - 1
        else
            dim = dimrec(W.weights, degree) - 1
        end
        new(sheaf, dim)
    end
end


struct WeightedProjectiveSpace
    W::Weights
    m::Int
    G::Float64
    embedding_dimension::Int
    embedding_linear_system::LinearSystem

    function WeightedProjectiveSpace(W::Weights)
        m_val = reduce(lcm, W.wellformed_weights)
        G_val = very_ample_bound(W.wellformed_weights)
        n = G_val / m_val < 0 ? 1 : ceil(Int, G_val / m_val)
        deg_mn = n * m_val
        linsys = LinearSystem(Weights(W.wellformed_weights), deg_mn)
        N = linsys.dimension
        new(W, m_val, G_val, N, linsys)
    end
end
