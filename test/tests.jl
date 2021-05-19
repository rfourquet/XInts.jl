using XInts
using XInts: Short, shortmin, shortmax, Limb, ClongMax, CulongMax, CdoubleMax
using BitIntegers

@testset "constructor" begin
    function test(a)
        x = XInt(a)
        @test x isa XInt
        if a isa XInt
            @test x === a
        else
            @test x == a
        end
        if !(a isa BigInt)
            @test x == BigInt(a)
        end
    end

    @testset "XInt(::XInt)" begin
        test(XInt(2))
        test(XInt(big(2)^200))
    end
    @testset "XInt(::Bool)" begin
        test(true)
        test(false)
    end

    @testset "XInt(::$T)" for T in [Base.BitInteger_types...,
                                    Int256, UInt256, Int512, UInt512, Int1024, UInt1024]
        for x = rand(T, 20)
            test(x)
        end
        for d = T[0, 1, 2]
            test(d)
            if T <: Signed
                test(-d)
            end
            test(typemin(T) + d)
            test(typemax(T) - d)
            test((typemax(T) >>> 1) + d)
            test((typemax(T) >>> 1) - d)
        end
    end

    @testset "XInt(::BigInt)" begin
        for T = (Bool, Int8, Int, Int128)
            for x = BigInt.(rand(T, 5))
                test(x)
            end
        end
    end

    @testset "XInt(::$F)" for F in [Float16, Float32, Float64]
        for T = (Bool, Int8, Int32)
            for x = F.(rand(T, 5))
                isinteger(x) && test(x)
            end
        end
        @test XInt(F(2.0)) === XInt(2)
        @test_throws InexactError XInt(F(2.2))
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

    @testset "BigInt(::XInt)" begin
        for T = (Bool, Int8, Int, Int128)
            for x = rand(T, 5)
                z = BigInt(x)
                y = XInt(x)
                @test z == BigInt(y) isa BigInt
                @test z == big(y) isa BigInt
                @test z == y % BigInt isa BigInt
            end
        end
    end

    @testset "$F(::XInt, $R)" for
        F in (Float16, Float32, Float64, BigFloat, AbstractFloat, float),
        R in ((F===float) ? ("",) : (RoundToZero, RoundDown, RoundUp, RoundNearest, ""))

        for T = Base.BitInteger_types
            for x = rand(T, 10)
                if R == ""
                    @test F(XInt(x)) == F(BigInt(x))
                    # have to use BigInt because of a Julia bug
                else
                    @test F(XInt(x), R) == F(BigInt(x), R)
                end
            end
        end
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

    @testset "iszero/isone" begin
        @test iszero(XInt(0))
        @test zero(XInt) === XInt(0)
        @test isone(XInt(1))
        @test one(XInt) === XInt(1)
        x = rand(Int8)
        @test iszero(x) == iszero(XInt(x))
        @test isone(x) == isone(XInt(x))
    end

    @testset "sign" begin
        @test sign(zero(XInt)) === XInt(0)
        @test signbit(zero(XInt)) === false
        @test signbit(one(XInt)) === false
        @test signbit(-one(XInt)) === true

        for x in rand(Int8, 10)
            y = XInt(x)
            @test sign(y) isa XInt
            @test sign(y) == sign(x)
            @test signbit(y) == signbit(x)
        end
    end

    @testset "digits" begin
        for r = big(2).^[5, 8, 64, 200]
            for b = rand(-r:r, 5)
                pad = rand(0:2)
                base = rand(8:12)
                @test ndigits(b, pad=pad, base=base) == ndigits(XInt(b), pad=pad, base=base)
                @test digits(b, pad=pad, base=base) == digits(XInt(b), pad=pad, base=base)
            end
        end
    end
end

@testset "misc" begin
    @testset "copy, signed, Signed, widen, hastypemax" begin
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
    end
    @testset "parse, string, show" begin
        @test parse(XInt, "123") === XInt(123)

        for x = BigInt[rand(Int8, 10); rand(Int128, 10); rand(-big(2)^200:big(2)^200, 10)]
            @test string(x) == string(XInt(x))
            @test sprint(show, x) == sprint(show, XInt(x))
        end
    end
    @testset "float(XInt)" begin
        @test float(XInt) === BigFloat
    end
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
        for a = (-x, x), b = (-y, y)
            s = if op === invmod
                    try
                        op(big(a), big(b))
                    catch
                        @test_throws DomainError op(XInt(a), XInt(b))
                        continue
                    end
                else
                    op(big(a), big(b))
                end
            r = op(XInt(a), XInt(b))
            if op === divrem
                @test r isa Tuple{XInt,XInt}
            elseif op === gcdx
                @test r isa Tuple{XInt,XInt,XInt}
            elseif !(s isa BigInt)
                @test typeof(s) == typeof(r)
            else
                @test r isa XInt
            end
            @test s == r
            if op === div
                for R = (RoundToZero, RoundDown, RoundUp)
                    @test div(big(a), big(b), R) == div(XInt(a), XInt(b), R) isa XInt
                end
            end
        end
    end
    @testset "$op(::XInt, ::XInt)" for op = (+, -, *, mod, rem, gcd, gcdx, lcm, &, |, xor,
                                             /, div, divrem, fld, cld, invmod,
                                             cmp, <, <=, >, >=, ==, flipsign, binomial)
        xs = Any[0, 1, 2, rand(0:1000, 10)..., shortmax, shortmax-1, shortmax-2,
                    rand(Int128(2)^65:Int128(2)^100, 2)..., rand(big(0):big(2)^200, 2)...,
                    shortmin] # TODO: shortmin and 0 are used twice when negated in test(...)
        for x=xs, y=xs
            iszero(y) && op ∈ (/, mod, rem, div, divrem, fld, cld, invmod) &&
                continue
            op === binomial && !all(0 .<= [x, y] .<= 1000) && continue
            test(op, x, y)
        end
    end

    function make_values(T, n=5)
        S = T === BigInt ? Int128 : T
        as = T[0, 1, 2, 3, rand(S, 2n)..., typemax(S), typemax(S)-1, typemax(S)-2]
        xs = BigInt.(filter(isinteger, as))
        if T <: Signed
            append!(as, (-).(as))
            push!(as, typemin(S))
        end
        if T <: Integer
            push!(xs, typemin(S))
            append!(xs, rand(S, 2n))
        end
        append!(xs, rand(big(2)^65:big(2)^100, n))
        append!(xs, rand(big(0):big(2)^200, n))
        as, xs
    end

    @testset "$op(::XInt, ::$T) / $op(::$T, ::XInt)" for
        op in (+, -, *, /, cmp, <, <=, >, >=, ==, flipsign, gcd, gcdx, binomial),
        T in [Base.uniontypes(CulongMax); Base.uniontypes(ClongMax);
             op ∈ (cmp, ) ? Base.uniontypes(CdoubleMax) : []]

        as, xs = make_values(T)
        for a = as, y = xs, z = (-y, y), x = (XInt(z),)
            op === binomial && !all(-1000 .<= [a, z] .<= 1000) && continue
            for (r, s) = ((op == binomial) ?
                          [(op(x, a), op(z, a))] : # TODO: remove special case
                          Any[(op(a, x), op(a, z)),
                              (op(x, a), op(z, a))])

                if s isa BigInt
                    @test r isa XInt
                elseif op === gcdx
                    @test r isa Tuple{XInt,XInt,XInt}
                else
                    @test typeof(r) == typeof(s)
                end
                @test isequal(r, s) # not `==` for NaN
            end
        end
    end

    @testset "powermod(::$T/XInt, ::$T/XInt, ::XInt)" for
            T in [Base.uniontypes(CulongMax); Base.uniontypes(ClongMax); [BigInt]]
        # TODO: add more combinations for first two parameters
        as1, xs1 = make_values(T, 2)
        as2, xs2 = make_values(T, 2)
        for a=as1, b=filter(>=(0), as2), x=filter(!iszero, xs1)
            s = powermod(a, b, x)
            r = powermod(a, b, XInt(x))
            @test s == r
            @test r isa XInt
        end
        for a=as1, x=filter(>=(0), xs1), y=filter(!iszero, xs2)
            s = powermod(a, x, y)
            r = powermod(a, XInt(x), XInt(y))
            @test s == r
            @test r isa XInt
            r = powermod(XInt(a), XInt(x), XInt(y))
            @test s == r
            @test r isa XInt
        end
    end
end

@testset "bit and unary ops, etc." begin
    xs = BigInt[0, 1, 2, 3, rand(UInt8, 5)..., rand(UInt, 5)..., rand(Short, 5)...,
                typemax(UInt), typemax(UInt)-1, typemax(UInt)-2,
                typemax(Short), typemax(Short)-1, typemax(Short)-2]
    append!(xs, rand(big(2)^65:big(2)^100, 5))
    append!(xs, rand(big(0):big(2)^200, 5))
    append!(xs, (-).(xs))
    push!(xs, typemin(Short), typemin(Short)+1, big(typemin(Short))-1)

    @testset "$op(::XInt)" for op = (-, ~, isqrt, trailing_zeros, trailing_ones, count_ones,
                                     abs, factorial)
        for x = xs
            op === factorial && !(0 <= x <= 1000) && continue
            s = try
                op(x)
            catch
                @test_throws Union{InexactError,DomainError,DivideError} op(XInt(x))
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
    @testset "$op(::XInt, c)" for op = (<<, >>, >>>, (^))
        for x = xs, T = [Base.BitInteger_types..., BigInt, Bool, XInt]
            for c = (T <: Signed && op !== (^) ? cs2 : T === Bool ? [true, false] : cs)
                s = op(x, T(c))
                r = op(XInt(x), T(c))
                @test s == r
                @test r isa XInt
            end
        end
    end
end
