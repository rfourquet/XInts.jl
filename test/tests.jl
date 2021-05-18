using XInts
using XInts: Short, shortmin, shortmax, Limb
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

@testset "addition" begin
    for _=1:20
        a, b = rand(big.(-1000:1000), 2)
        @test string(a+b) == string(XInt(a) + XInt(b)) == string(XInt(b) + XInt(a))
    end
    for (a, b) = [(big(typemax(Short)-1), big(1)), # no overflow
                  (big(typemax(Short)-1), big(2)), # overflow
                  rand(big(2)^65:big(2)^100, 2), # two bigs
                  rand(big(0):big(2)^100, 2)] # anything
        for _=1:2
            for (a, b) = [(a, b), (-a, b), (a, -b), (-a, -b)]
                @test string(a+b) == string(XInt(a) + XInt(b))
            end
            a, b = b, a
        end
    end
end
