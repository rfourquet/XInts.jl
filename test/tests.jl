using XInts
using XInts: Short, shortmin, shortmax, Limb, ClongMax, CulongMax
using BitIntegers

@testset "constructor" begin
    @testset "XInt(::XInt)" begin
        x = XInt(2)
        @test XInt(x) === x
        x = XInt(big(2)^200)
        @test XInt(x) === x
    end
    @testset "XInt(::Bool)" begin
        @test XInt(false) == BigInt(false)
        @test XInt(true) == BigInt(true)
    end

    @testset "XInt(::$T)" for T in [Base.BitInteger_types...,
                                    Int256, UInt256, Int512, UInt512, Int1024, UInt1024]
        for x = rand(T, 40)
            @test XInt(x) == BigInt(x)
        end
        for d = T[0, 1, 2]
            x = typemin(T) + d
            y = typemax(T) - d
            @test XInt(x) == BigInt(x)
            @test XInt(y) == BigInt(y)
            @test XInt(d) == BigInt(d)
            if T <: Signed
                @test XInt(-d) == BigInt(-d)
            end
            x = (typemax(T) >>> 1) + d
            y = (typemax(T) >>> 1) - d
            @test XInt(x) == BigInt(x)
            @test XInt(y) == BigInt(y)
        end
    end

    @testset "XInt(::$T)" for T in [Float16, Float32, Float64]
        @test XInt(T(2.0)) === XInt(2)
        @test_throws InexactError XInt(T(2.2))
    end
end

@testset "conversions" begin
    @testset "rem(::XInt, ::Type{Bool})" begin
        for x = Any[rand(Limb), big(rand(Int128)), rand(-big(2)^200:big(2)^200)]
            @test XInt(x) % Bool === x % Bool
        end
    end
    @testset "rem(::XInt, ::Type{$T})" for T in Base.BitInteger_types
        xs = T[0, 2, rand(T, 10)..., typemax(T)]
        if T <: Signed
            push!(xs, -1, -2, typemin(T))
        end
        for x = xs
            @test XInt(x) % T === x
            @test XInt(big(rand(T)) << (8*sizeof(T)) +
                       big(x)) % T === x
            @test XInt(big(rand(T)) << (16*sizeof(T)) +
                       big(rand(T)) << (8*sizeof(T)) +
                       big(x)) % T === x
        end
    end

    @testset "Bool(::XInt)" begin
        @test Bool(XInt(0)) == false
        @test Bool(XInt(1)) == true
        for x = Any[rand(Int8, 10); rand(Int128, 10)]
            (x == 0 || x == 1) && continue
            @test_throws InexactError Bool(XInt(x))
        end
    end
    @testset "$T(::XInt)" for T in Base.BitInteger_types
        for x = rand(T, 10)
            @test T(XInt(x)) === x
        end
        if sizeof(T) > sizeof(Short)
            for x = T.(rand(T <: Signed ? Int32 : UInt32, 10))
                @test T(XInt(x)) === x
            end
        end
        @test T(XInt(typemax(T))) === typemax(T)
        @test T(XInt(typemin(T))) === typemin(T)
        @test_throws InexactError T(XInt(typemax(T))+XInt(1))
        @test_throws InexactError T(XInt(typemax(T))+XInt(+10))
        @test_throws InexactError T(XInt(typemin(T))+XInt(-1))
        @test_throws InexactError T(XInt(typemin(T))+XInt(-10))
    end
end

@testset "math" begin
    @testset "isodd/iseven" begin
        for x = Any[rand(Int8, 5)...,
                    rand((-1, 1)) .* rand(0:big(2)^200, 5)...]
            y = XInt(x)
            @test iseven(y) == iseven(x) != isodd(y)
        end
    end
end

@testset "misc" begin
    # automatic implementation from XInt <: Signed
    for x = XInt[2, big(2)^70]
        @test copy(x) === x
        @test signed(x) === x
        @test Signed(x) === x
        @test widen(x) === x
    end
    @test widen(XInt) == XInt
    @test !Base.hastypemax(XInt)
    if VERSION >= v"1.5"
        @test signed(XInt) == XInt
    end
    @test parse(XInt, "123") === XInt(123)
end

@testset "trunc" begin
    for T in [#=Float16,=# Float32, Float64] # TODO: add Float16, and also for BigInt
        @test trunc(XInt, T(2.2)) === XInt(2)
        @test trunc(XInt, T(-2.2)) === XInt(-2)
        @test_throws InexactError trunc(XInt, T(NaN))
        @test_throws InexactError trunc(XInt, T(Inf))
        @test unsafe_trunc(XInt, T(2.2)) === XInt(2)
        @test unsafe_trunc(XInt, T(-2.2)) === XInt(-2)
    end
end

@testset "comparisons" begin
    @testset "==" begin
        xs = BigInt[shortmin, 0, 1, 2, shortmax-1, shortmax, shortmax+1, big(2)^100]
        xs = [xs..., (-).(xs)...]
        for (a, b) in Iterators.product(xs, xs)
            x, y = XInt(a), XInt(b)
            @test x == x
            @test (a == b) == (x == y)
            @test a == x && x == a
            @test b == y && y == b
            for T in Base.BitInteger_types
                if typemin(T) <= b <= typemax(T)
                    z = T(b)
                    @test (x == z) == (a == z) == (z == x)
                end
            end
        end
    end
end

@testset "operations" begin
    function test(op, x, y)
        for x = (-x, x), y = (-y, y), a = (x, y), b = (x, y)
            s = if op === invmod
                    try
                        op(a, b)
                    catch DomainError
                        nothing
                    end
                else
                    op(a, b)
                end
            if s === nothing # can't be put in the catch branch above, it fails
                             # when is_short branch is taken
                             # TODO: can this be fixed ? (error message is confusing...)
                @test_throws DomainError op(XInt(a), XInt(b))
                continue
            end
            r = op(XInt(a), XInt(b))
            if op === /
                @test r isa BigFloat
            elseif op === divrem
                @test r isa Tuple{XInt,XInt}
            else
                @test r isa XInt
            end
            @test s == r
            if op === div
                for R = (RoundToZero, RoundDown, RoundUp)
                    @test div(a, b, R) == div(XInt(a), XInt(b), R) isa XInt
                end
            end
        end
    end
    @testset "$op(::XInt, ::XInt)" for op = (+, -, *, mod, rem, gcd, lcm, &, |, xor,
                                             /, div, divrem, fld, cld, invmod)
        for _=1:20
            a, b = rand(big.(0:1000), 2)
            test(op, a, b)
        end
        for (a, b) = [(big(typemax(Short)-1), big(1)), # no overflow
                      (big(typemax(Short)-1), big(2)), # overflow
                      rand(big(2)^65:big(2)^100, 2), # two bigs
                      rand(big(0):big(2)^100, 2)] # anything
            test(op, a, b)
        end
    end
    @testset "$op(::XInt, ::$T) / $op(::$T, ::XInt)" for op = (+, -, *, /),
                                                         T = [Base.uniontypes(CulongMax);
                                                              Base.uniontypes(ClongMax)]
        as = T[0, 1, 2, 3, rand(T, 10)..., typemax(T), typemax(T)-1, typemax(T)-2]
        xs = BigInt.(as)
        if T <: Signed
            append!(as, (-).(as))
            push!(as, typemin(T))
        end
        push!(xs, typemin(T))
        append!(xs, rand(T, 10))
        append!(xs, rand(big(2)^65:big(2)^100, 5))
        append!(xs, rand(big(0):big(2)^200, 5))
        for a = as, y = xs, z = (-y, y), x = (XInt(z),)
            for (r, s) = Any[(op(a, x), op(a, z)),
                             (op(x, a), op(z, a))]

                r = op(a, x)
                s = op(a, z)
                if op === /
                    @test r isa BigFloat
                else
                    @test r isa XInt
                end
                @test isequal(r, s) # not `==` for NaN
            end
        end
    end
end

@testset "bitops and unary (-)" begin
    xs = BigInt[0, 1, 2, 3, rand(UInt8, 5)..., rand(UInt, 5)..., rand(Short, 5)...,
                typemax(UInt), typemax(UInt)-1, typemax(UInt)-2,
                typemax(Short), typemax(Short)-1, typemax(Short)-2]
    append!(xs, rand(big(2)^65:big(2)^100, 5))
    append!(xs, rand(big(0):big(2)^200, 5))
    append!(xs, (-).(xs))
    push!(xs, typemin(Short), typemin(Short)+1, big(typemin(Short))-1)

    @testset "$op(::XInt)" for op = (-, ~, trailing_zeros, trailing_ones, count_ones)
        for x = xs
            s = try
                op(x)
            catch InexactError
                nothing
            end
            if s === nothing
                @test_throws Union{InexactError,DomainError} op(XInt(x))
                continue
            end
            r = op(XInt(x))
            @test r == s
            if s isa BigInt
                @test r isa XInt
            else
                @assert s isa Int
                @test r isa Int
            end
        end
    end
    cs = [0, 1, 2, 3, 4, rand(5:typemax(Int8), 20)...]
    cs2 = [cs; (-).(cs)]
    @testset "$op(::XInt, c)" for op = (<<, >>, >>>)
        for x = xs, T = [Base.BitInteger_types..., BigInt], c = (T <: Signed ? cs2 : cs)
            s = op(x, T(c))
            r = op(XInt(x), T(c))
            @test s == r
            @test r isa XInt
        end
    end
end
