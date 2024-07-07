/**
 * Author: Timothy Herchen (anematode) - 3 July 2024
 * Compile using: g++ lc_interpret.cpp -o lc_interpret -O3 -Wall -Wextra -std=c++20
 * Usage: lc_interpret <input.lc>
 */

#include <cstring>
#include <utility>
#include <variant>
#include <vector>
#include <fstream>
#include <span>
#include <unordered_map>
#include <cassert>

struct LambdaTerm;

void DestructLambdaTerm(LambdaTerm *term);

using LambdaVariableId = uint32_t;

struct BumpAllocator {
    // 4 byte reference count, lambda term
    uint8_t *bytes;
    uint8_t *end;

    // Lambda term pointers which may be reused
    std::vector<uint8_t *> free_list;

    explicit BumpAllocator(size_t size) {
        bytes = new uint8_t[size];
        end = bytes + size;
    }

    LambdaTerm *NewTermUninit(size_t lambda_term_size) {
        if (!free_list.empty()) {
            auto *term = (LambdaTerm *) free_list.back();
            free_list.pop_back();
            return term;
        }

        int *ref_count = (int *) allocate(sizeof(int) + lambda_term_size);
        *ref_count = 0;
        return (LambdaTerm *) (ref_count + 1);
    }

    void IncrRef(const LambdaTerm *term) {
        int *ref_count = (int *) ((uintptr_t) term - sizeof(int));
        (*ref_count)++;
    }

    void DecrRef(LambdaTerm *term) {
        int *ref_count = (int *) ((uintptr_t) term - sizeof(int));
        (*ref_count)--;

        if (*ref_count == 0) { // manually call destructor
            DestructLambdaTerm(term);
            free_list.push_back((uint8_t *) term);
        }
    }

    uint8_t *allocate(size_t count) {
        count = (count + 7) & ~7;  // round to multiple of 8
        if ((uintptr_t) bytes + count > (uintptr_t) end) {
            throw std::runtime_error("Out of memory");
        }
        uint8_t *result = bytes;
        bytes += count;
        return result;
    }
};

BumpAllocator allocator{1ULL << 30};

struct SharedTerm {
    LambdaTerm *term;

    SharedTerm(LambdaTerm *term) : term(term) {
        allocator.IncrRef(term);
    }

    SharedTerm(const SharedTerm &other) : term(other.term) {
        allocator.IncrRef(term);
    }

    SharedTerm(SharedTerm &&other) noexcept: term(other.term) {
        other.term = nullptr;
    }

    ~SharedTerm() {
        if (term) {
            allocator.DecrRef(term);
        }
    }

    SharedTerm &operator=(const SharedTerm &other) {
        if (term)
            allocator.DecrRef(term);
        term = other.term;
        allocator.IncrRef(term);
        return *this;
    }

    SharedTerm &operator=(SharedTerm &&other) noexcept {
        if (term)
            allocator.DecrRef(term);
        term = other.term;
        other.term = nullptr;
        return *this;
    }

    const LambdaTerm *operator->() const {
        return term;
    }

    LambdaTerm *operator->() {
        return term;
    }
};

struct LambdaVariable {
    LambdaVariableId id;

    LambdaVariable(LambdaVariableId id) : id(id) {}
};

struct LambdaAbstraction {
    LambdaVariableId id;
    SharedTerm term;
};

struct LambdaApplication {
    SharedTerm lhs;
    SharedTerm rhs;
};

struct ReductionResult {
    SharedTerm term;
    bool changed;
};

static uint64_t RNG = 0x1234;  // used to randomly select free variable names

class FreeBitset {
public:
    constexpr static int MAX_FREE = 256;
    static_assert(MAX_FREE % 64 == 0);
    std::array<uint64_t, MAX_FREE / 64> data;

    bool Test(unsigned index) const {
        assert(index < MAX_FREE);
        return data[index >> 6] & (1ULL << (index & 0x3f));
    }

    static void Or(const FreeBitset &a, const FreeBitset &b, FreeBitset &result) {
        for (size_t i = 0; i < a.data.size(); ++i)
            result.data[i] = a.data[i] | b.data[i];
    }

    void Enable(unsigned index) {
        assert(index < MAX_FREE);
        data[index >> 6] |= 1ULL << (index & 0x3f);
    }

    void Disable(unsigned index) {
        assert(index < MAX_FREE);
        data[index >> 6] &= ~(1ULL << (index & 0x3f));
    }

    uint32_t RandomUnused() const {
        // Select randomly to reduce chance of lots of rewrites after repeated alpha conversions
        uint32_t rng = (RNG = ((RNG * 0x314159265ULL) + 0x12345) >> 20) % MAX_FREE;
        for (int i = 0; i < MAX_FREE; ++i) {
            unsigned j = ((rng + i) % (MAX_FREE - 128)) + 128;  // don't re-assign named variables
            if (!Test(j))
                return j;
        }
        throw std::runtime_error("Ran out of free variables!");
    }

    bool Empty() const {
        return std::all_of(data.begin(), data.end(), [&](uint64_t a) { return a == 0; });
    }
};

struct LambdaTerm {
    std::variant<LambdaVariable, LambdaAbstraction, LambdaApplication> term;
    FreeBitset free{};  // bitset of free variables
    FreeBitset used{};  // bitset of variables (free or nonfree) mentioned somewhere -- unsafe to be used as the target of an alpha

    // Whether this term may contain more beta reductions
    bool may_reduce;

    LambdaTerm(decltype(term) in) : term(std::move(in)) {
        if (auto *var = std::get_if<LambdaVariable>(&term)) {
            free.Enable(var->id);
            used = free;
            may_reduce = false;
        } else if (auto *abs = std::get_if<LambdaAbstraction>(&term)) {
            free = abs->term->free;
            free.Disable(abs->id);   // variable now bound, and no longer free ...
            used = abs->term->used;
            used.Enable(abs->id);    // ... but is mentioned, so can't be safe target of alpha conversion
            may_reduce = abs->term->may_reduce;
        } else {
            auto &app = std::get<LambdaApplication>(term);
            FreeBitset::Or(app.lhs->free, app.rhs->free, free);
            FreeBitset::Or(app.lhs->used, app.rhs->used, used);
            may_reduce = app.lhs->may_reduce || app.rhs->may_reduce ||
                         std::holds_alternative<LambdaAbstraction>(app.lhs->term);
        }
    }

    static SharedTerm NewSharedTerm(decltype(term)&& term) {
        return {new(allocator.NewTermUninit(sizeof(LambdaTerm))) LambdaTerm(term)};
    }

    std::string ToString(const std::unordered_map<LambdaVariableId, std::string> &id_to_var) const {
        auto PrintVar = [&id_to_var](LambdaVariableId id) -> std::string {
            auto f = id_to_var.find(id);
            if (f == id_to_var.end()) // result of an alpha conversion -- variable not original
                return "var$" + std::to_string(id);
            return f->second;
        };

        if (auto *var = std::get_if<LambdaVariable>(&term)) {
            return PrintVar(var->id);
        } else if (auto *abs = std::get_if<LambdaAbstraction>(&term)) {
            // e.g. (\x. 3), conservatively parenthesised
            return "(\\" + PrintVar(abs->id) + ". " + abs->term->ToString(id_to_var) + ")";
        } else {
            LambdaApplication app = std::get<LambdaApplication>(term);
            return "(" + app.lhs->ToString(id_to_var) + " " + app.rhs->ToString(id_to_var) + ")";
        }
    }

    std::optional<SharedTerm> AlphaConversion(LambdaVariableId variable_id, LambdaVariableId new_id) {
        if (auto *var = std::get_if<LambdaVariable>(&term)) {
            if (var->id == variable_id)
                return LambdaTerm::NewSharedTerm(LambdaVariable{new_id});
            return std::nullopt;
        } else if (auto *v = std::get_if<LambdaAbstraction>(&term)) {
            if (v->id == variable_id)
                return std::nullopt; // no longer free on the RHS
            return LambdaTerm::NewSharedTerm(
                    LambdaAbstraction{v->id, v->term->AlphaConversion(variable_id, new_id).value_or(v->term)}
            );
        } else {
            LambdaApplication abs = std::get<LambdaApplication>(term);
            return LambdaTerm::NewSharedTerm(
                    LambdaApplication{
                            abs.lhs->AlphaConversion(variable_id, new_id).value_or(abs.lhs),
                            abs.rhs->AlphaConversion(variable_id, new_id).value_or(abs.rhs)
                    }
            );
        }
    }

    // Perform the substitution variable -> subst on the given term, returning a new term if the term has changed
    ReductionResult
    BetaReduce(LambdaVariableId variable_id, SharedTerm &subst) {
        if (free.Empty()) { // pass
        } else if (auto *v = std::get_if<LambdaVariable>(&term)) {
            if (v->id == variable_id)
                return {subst, true};
        } else if (auto *abs = std::get_if<LambdaAbstraction>(&term)) {
            if (abs->id != variable_id) {
                if (!subst->free.Test(abs->id)) {
                    auto reduced = abs->term->BetaReduce(variable_id, subst);
                    if (reduced.changed)
                        return {LambdaTerm::NewSharedTerm(LambdaAbstraction{abs->id, reduced.term}), true};
                } else {
                    auto new_id = abs->term->used.RandomUnused();

                    auto converted = abs->term->AlphaConversion(abs->id, new_id)
                            .value_or(abs->term);
                    auto reduced = converted->BetaReduce(variable_id, subst);

                    return {LambdaTerm::NewSharedTerm(LambdaAbstraction{new_id, reduced.term}), true};
                }
            }
        } else {
            LambdaApplication app = std::get<LambdaApplication>(term);
            auto lhs = app.lhs->BetaReduce(variable_id, subst);
            // not strictly normal order but *shrug*
            auto rhs = app.rhs->BetaReduce(variable_id, subst);

            if (lhs.changed || rhs.changed)
                return {LambdaTerm::NewSharedTerm(LambdaApplication{lhs.term, rhs.term}), true};
        }

        return {this, false};  // no change
    }

    ReductionResult ReduceNormalOrder() {
        if (!may_reduce) return {this, false};
        if (auto *app = std::get_if<LambdaApplication>(&term)) {
            if (auto *abs = std::get_if<LambdaAbstraction>(&app->lhs->term)) {
                // Abstraction applied to application -> beta reduce
                auto result = abs->term->BetaReduce(abs->id, app->rhs);
                return {result.term, true};
            }

            // Visit LHS, then RHS
            auto lhs = app->lhs->ReduceNormalOrder();
            if (lhs.changed)
                return {LambdaTerm::NewSharedTerm(LambdaApplication{lhs.term, app->rhs}), true};

            auto rhs = app->rhs->ReduceNormalOrder();
            if (rhs.changed)
                return {LambdaTerm::NewSharedTerm(LambdaApplication{app->lhs, rhs.term}), true};
        } else if (auto *abs = std::get_if<LambdaAbstraction>(&term)) {
            // Visit contents of lambda abstraction
            auto result = abs->term->ReduceNormalOrder();
            if (result.changed)
                return {LambdaTerm::NewSharedTerm(LambdaAbstraction{abs->id, result.term}), true};
        }

        may_reduce = false;
        return {this, false};
    }
};

void DestructLambdaTerm(LambdaTerm *term) {
    term->~LambdaTerm();
}

bool ValidVariableChar(char c) {
    auto valid = "*+-_/<>~!^%&=?";  // per Will's interpreter.scm
    return isalnum(c) || strchr(valid, c) != nullptr;
}

using LcToken = std::variant<char, std::string>;

std::vector<LcToken> Tokenize(const std::string &input) {
    std::string s = "(" + input + ")";
    std::vector<LcToken> result;
    for (size_t i = 0; i < s.size(); ++i) {
        char c = s[i];
        if (c == '(' || c == ')' || c == '\\' || c == '.') {
            result.emplace_back(c);
        } else if (isspace(c)) {
            continue;
        } else {
            std::string token;
            while (i < s.size() && ValidVariableChar(c = s[i])) {
                token.push_back(c);
                ++i;
            }
            if (token.empty())
                throw std::runtime_error("Invalid character at index " + std::to_string(i) + " in " + s);
            result.emplace_back(token);
            --i;
        }
    }
    return result;
}

std::string ExpectVariable(std::span<const LcToken> &tokens) {
    if (tokens.empty() || !std::holds_alternative<std::string>(tokens[0]))
        throw std::runtime_error("Expected variable");
    std::string var = std::get<std::string>(tokens[0]);
    tokens = tokens.subspan(1);
    return var;
}

void ExpectChar(std::span<const LcToken> &tokens, char c, const char *error) {
    if (tokens.empty() || !std::holds_alternative<char>(tokens[0]) || std::get<char>(tokens[0]) != c)
        throw std::runtime_error(error);
    tokens = tokens.subspan(1);
}

SharedTerm ParseLambdaTerm(std::span<const LcToken> &tokens,
                           std::unordered_map<std::string, LambdaVariableId> &vars,
                           std::unordered_map<LambdaVariableId, int /* count */> &bound_vars) {
    if (tokens.empty())
        throw std::runtime_error("Unexpected EOF");

    auto token = tokens[0];
    tokens = tokens.subspan(1);

    if (const auto *var = std::get_if<std::string>(&token)) {
        auto it = vars.find(*var);
        if (it == vars.end())
            throw std::runtime_error("Unbound variable " + *var);

        return LambdaTerm::NewSharedTerm(LambdaVariable{it->second});
    } else if (const auto *c = std::get_if<char>(&token)) {
        if (*c == '(') {  // group or function application
            auto first = ParseLambdaTerm(tokens, vars, bound_vars);
            if (tokens.empty())
                throw std::runtime_error("Unexpected end of input");
            if (const auto *next = std::get_if<char>(&tokens[0])) {
                if (*next == ')') { // end of a grouping
                    tokens = tokens.subspan(1);
                    return first;
                }
            }

            auto second = ParseLambdaTerm(tokens, vars, bound_vars);
            ExpectChar(tokens, ')', "Expected closing parenthesis for function application");

            return LambdaTerm::NewSharedTerm(LambdaApplication{first, second});
        } else if (*c == '\\') {
            std::string arg = ExpectVariable(tokens);
            ExpectChar(tokens, '.', "Expected dot after abstraction variable");

            if (vars.find(arg) == vars.end()) {
                vars[arg] = vars.size();  // allocate new variable
                if (vars.size() >= FreeBitset::MAX_FREE)
                    throw std::runtime_error("Too many distinct variable names");
            }

            bound_vars[vars[arg]]++;
            SharedTerm term = ParseLambdaTerm(tokens, vars, bound_vars);
            bound_vars[vars[arg]]--;

            return LambdaTerm::NewSharedTerm(LambdaAbstraction{vars.at(arg), term});
        } else {
            throw std::runtime_error("Unexpected character " + std::string(1, *c));
        }
    }

    throw std::runtime_error("Unreachable");
}

int main(int argc, char **argv) {
    if (argc < 2) {
        fprintf(stderr, "Usage: %s <input.lc>\n", argv[0]);
        exit(1);
    }

    std::ifstream file(argv[1]);
    if (!file.is_open())
        throw std::runtime_error(std::string("Failed to open file ") + argv[1]);

    auto text = std::string(std::istreambuf_iterator<char>(file), std::istreambuf_iterator<char>());
    auto tokens = Tokenize(text);

    std::unordered_map<std::string, LambdaVariableId> vars;
    std::unordered_map<LambdaVariableId, int /* count */> bound_vars;
    std::span<const LcToken> token_span(tokens.data(), tokens.size());

    SharedTerm current_term = ParseLambdaTerm(token_span, vars, bound_vars);

    if (!token_span.empty())
        throw std::runtime_error("Trailing tokens");

    unsigned reductions = 0;
    while (true) {
        auto [result, changed] = current_term->ReduceNormalOrder();
        if (!changed) break;
        current_term = result;
        reductions++;
    }

    std::unordered_map<LambdaVariableId, std::string> id_to_var;
    for (const auto &[var, id]: vars)
        id_to_var[id] = var;

    puts(current_term->ToString(id_to_var).c_str());
    printf("Reductions: %u\n", reductions);
    return 0;
}