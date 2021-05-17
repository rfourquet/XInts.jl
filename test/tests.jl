using XInts
using XInts: Short

const shortmin = typemin(Short)
const shortmax = typemax(Short)

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
