using XInts
using XInts: Short, shortmin, shortmax
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
