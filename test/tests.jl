using XInts
using XInts: Short

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
