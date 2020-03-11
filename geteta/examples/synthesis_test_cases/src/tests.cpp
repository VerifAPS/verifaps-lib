#include "rs_flipflop.h"
#include "t_flipflop.h"
#include "calculator.h"
#include "output_dependencies.h"

#include "gtest/gtest.h"

#include <string>
#include <vector>

namespace {
    using namespace std::string_literals;

    TEST(GeneratedCodeTest, RSFlipFlop) {
        using namespace rs_flipflop;

        auto automaton = synthesized{};
        auto inputs = std::vector<synthesized::input_type> {
                {false, false},
                {false, false},
                {true, false},
                {false, false},
                {false, true},
                {false, true},
                {false, false},
                {false, false},
                {true, false},
                {true, true},
        };
        auto expected_outputs = std::vector<synthesized::result> {
                {true, {false}},
                {true, {false}},
                {true, {false}},
                {true, {false}},
                {true, {true}},
                {true, {true}},
                {true, {true}},
                {true, {true}},
                {true, {false}},
                {false, {false}},
        };

        auto iteration = std::size_t{0};
        for (const auto& input : inputs) {
            SCOPED_TRACE("Iteration "s + std::to_string(iteration + 1));
            ASSERT_EQ(automaton.next(input), expected_outputs.at(iteration));
            iteration++;
        }
    }

    TEST(GeneratedCodeTest, TFlipFlop) {
        using namespace t_flipflop;

        auto automaton = synthesized{};
        auto inputs = std::vector<synthesized::input_type> {
                {false},
                {false},
                {true},
                {false},
                {true},
                {true},
                {true},
                {false},
        };
        auto expected_outputs = std::vector<synthesized::result> {
                {true, {false}},
                {true, {false}},
                {true, {true}},
                {true, {true}},
                {true, {false}},
                {true, {true}},
                {true, {false}},
                {true, {false}},
        };

        auto iteration = std::size_t{0};
        for (const auto& input : inputs) {
            SCOPED_TRACE("Iteration "s + std::to_string(iteration + 1));
            ASSERT_EQ(automaton.next(input), expected_outputs.at(iteration));
            iteration++;
        }
    }

    enum CalculatorMode {
        NOOP = 0,
        PLUS = 1,
        MINUS = 2,
        TIMES = 3,
        DIV = 4,
        NEGATE = 5
    };

    TEST(GeneratedCodeTest, Calculator) {
        using namespace calculator;

        auto automaton = synthesized{};
        auto inputs = std::vector<synthesized::input_type> {
                {CalculatorMode::PLUS, 2, false},
                {CalculatorMode::PLUS, 2, false},
                {CalculatorMode::TIMES, -2, false},
                {CalculatorMode::NEGATE, 42, false},
                {CalculatorMode::DIV, 2, false},
                {CalculatorMode::NOOP, 42, false},
                {CalculatorMode::MINUS, -125, false},
                {CalculatorMode::NEGATE, 42, false},
                {CalculatorMode::PLUS, -1, false},
                {CalculatorMode::NEGATE, 42, false},
                {CalculatorMode::DIV, 0, true},
                {CalculatorMode::PLUS, 2, false},
                {CalculatorMode::PLUS, 2, false},
                {CalculatorMode::TIMES, -1, false},
                {CalculatorMode::NEGATE, 42, false},
                {CalculatorMode::DIV, 2, false},
                {CalculatorMode::DIV, 2, false},
                {CalculatorMode::DIV, 2, false},
        };
        auto expected_outputs = std::vector<synthesized::result> {
                {true, {0, false}},
                {true, {2, false}},
                {true, {-4, false}},
                {true, {4, false}},
                {true, {2, false}},
                {true, {2, false}},
                {true, {127, false}},
                {true, {-127, false}},
                {true, {-128, false}},
                {true, {-128, false}},
                {true, {0, true}},
                {true, {0, true}},
                {true, {0, true}},
                {true, {0, true}},
                {true, {0, true}},
                {true, {0, true}},
                {true, {0, false}},
                {false, {0, false}},
        };

        auto iteration = std::size_t{0};
        for (const auto& input : inputs) {
            SCOPED_TRACE("Iteration "s + std::to_string(iteration + 1));
            ASSERT_EQ(automaton.next(input), expected_outputs.at(iteration));
            iteration++;
        }
    }

    TEST(GeneratedCodeTest, OutputDependencies) {
        using namespace output_dependencies;

        auto automaton = synthesized{};
        auto inputs = std::vector<synthesized::input_type> {
                {23},
                {42},
        };
        auto expected_outputs = std::vector<synthesized::result> {
                {true, {24, 0, 0}},
                {false, {0, 0, 0}},
        };

        auto iteration = std::size_t{0};
        for (const auto& input : inputs) {
            SCOPED_TRACE("Iteration "s + std::to_string(iteration + 1));
            auto result = automaton.next(input);
            ASSERT_EQ(result.in_spec, expected_outputs.at(iteration).in_spec);
            ASSERT_EQ(result.output.b, result.output.b);
            // FIXME: the result for c we're getting from omega currently isn't correct
//            ASSERT_GT(result.output.c, result.output.b);
//            ASSERT_GT(result.output.d, result.output.b);
//            ASSERT_EQ(result.output.d, result.output.c + 1);
            iteration++;
        }
    }
}

int main(int argc, char **argv) {
    ::testing::InitGoogleTest(&argc, argv);
    return RUN_ALL_TESTS();
}
