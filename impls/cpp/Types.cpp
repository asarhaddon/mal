#include "Debug.h"
#include "Types.h"
#include "Validation.h"

template<class T>
T* value_cast(const String& context, malValuePtr obj, const char* typeName)
{
    T* dest = dynamic_cast<T*>(obj);
    MAL_CHECK(dest != NULL, "%s: %s is not a %s", context.c_str(),
              obj->print(true).c_str(), typeName);
    return dest;
}
#define INSTANTIATE_VALUE_CAST(T) \
  template T* value_cast<T>(const String&, malValuePtr, const char*)
INSTANTIATE_VALUE_CAST(malApplicable);
INSTANTIATE_VALUE_CAST(malAtom);
INSTANTIATE_VALUE_CAST(malHash);
INSTANTIATE_VALUE_CAST(malInteger);
INSTANTIATE_VALUE_CAST(malLambda);
INSTANTIATE_VALUE_CAST(malList);
INSTANTIATE_VALUE_CAST(malSequence);
INSTANTIATE_VALUE_CAST(malString);
INSTANTIATE_VALUE_CAST(malSymbol);

namespace mal {
    malValuePtr atom(malValuePtr value) {
        return malValuePtr(new malAtom(value));
    };

    malValuePtr boolean(bool value) {
        return value ? trueValue() : falseValue();
    }

    malValuePtr builtin(const String& name, malBuiltIn::ApplyFunc handler) {
        return malValuePtr(new malBuiltIn(name, handler));
    };

    malValuePtr falseValue() {
        static malValuePtr c(new malConstant("false"));
        return malValuePtr(c);
    };

    malValuePtr hash(malValueIter argsBegin, malValueIter argsEnd,
                     const String& context) {
        return malValuePtr(new malHash(argsBegin, argsEnd, context));
    }

    malValuePtr integer(int64_t value) {
        return malValuePtr(new malInteger(value));
    };

    malValuePtr integer(const String& token) {
        return integer(std::stoi(token));
    };

    malValuePtr keyword(const String& token) {
        return malValuePtr(new malKeyword(token));
    };

    malValuePtr lambda(malLambda::ApplyFunc apply,
                       const StringVec& bindings,
                       malValuePtr body, malEnvPtr env) {
        return malValuePtr(new malLambda(apply, bindings, body, env));
    }

    malValuePtr list(malValueIter begin, malValueIter end) {
        return malValuePtr(new malList(begin, end));
    };

    malValuePtr list() {
        static malValuePtr c = malValuePtr(new malList());
        return malValuePtr(c);
    }

    malValuePtr list(malValuePtr a, malValuePtr b) {
        auto items = new malList();
        items->push_back(a);
        items->push_back(b);
        return malValuePtr(items);
    }

    malValuePtr list(malValuePtr a, malValuePtr b, malValuePtr c) {
        auto items = new malList();
        items->push_back(a);
        items->push_back(b);
        items->push_back(c);
        return malValuePtr(items);
    }

    malValuePtr macro(const malLambda& lambda) {
        return lambda.asMacro();
    };

    malValuePtr nilValue() {
        static malValuePtr c(new malConstant("nil"));
        return malValuePtr(c);
    };

    malValuePtr string(const String& token) {
        return malValuePtr(new malString(token));
    }

    malValuePtr symbol(const String& token) {
        return malValuePtr(new malSymbol(token));
    };

    malValuePtr trueValue() {
        static malValuePtr c(new malConstant("true"));
        return malValuePtr(c);
    };

    malValuePtr vector(malValueIter begin, malValueIter end) {
        return malValuePtr(new malVector(begin, end));
    };
};

malAtom::malAtom(malValuePtr value) : m_value(value) { }
malValuePtr malAtom::deref() const { return m_value; }
malValuePtr malAtom::reset(malValuePtr value) { return m_value = value; }
String malAtom::print(bool readably) const
{
    return STRF("(atom %s)", m_value->print(readably).c_str());
}

malBuiltIn::malBuiltIn(const String&name, ApplyFunc* apply, malValuePtr meta)
  : malApplicable(meta), m_name(name), m_handler(apply) { }

malValuePtr malBuiltIn::apply(malValueIter argsBegin,
                              malValueIter argsEnd) const
{
    return m_handler(m_name, argsBegin, argsEnd);
}

malValuePtr malBuiltIn::doWithMeta(malValuePtr meta) const
{
    return malValuePtr(new malBuiltIn(m_name, m_handler, meta));
}
String malBuiltIn::name() const { return m_name; }
String malBuiltIn::print(bool) const
{
    return STRF("#builtin-function(%s)", m_name.c_str());
}

malConstant::malConstant(String name) : m_name(name) { }
bool malConstant::doIsEqualTo(const malValue* rhs) const
{
    return this == rhs; // these are singletons
}
String malConstant::print(bool) const { return m_name; }

bool malHash::malKeyEqual::operator()(const malValuePtr& lhs,
                                      const malValuePtr& rhs) const
{
    return lhs->doIsEqualTo(rhs);
}

size_t malHash::malKeyHash::operator()(const malValuePtr& key) const
{
    if (const malString* skey = DYNAMIC_CAST(malString, key)) {
        return std::hash<String>{}(skey->print(true));
    }
    else if (const malKeyword* kkey = DYNAMIC_CAST(malKeyword, key)) {
        return std::hash<String>{}(kkey->print(true));
    }
    MAL_FAIL("%s is not a string or keyword", key->print(true).c_str());
}

void malHash::addToMap(malValueIter argsBegin, malValueIter argsEnd,
                       const String& context)
{
    // This is intended to be called with pre-evaluated arguments.
    checkArgsEven(context.c_str(), std::distance(argsBegin, argsEnd));
    for (auto it = argsBegin; it != argsEnd; ++it) {
        auto key = *it++;
        m_map[key] = *it;
    }
}

malHash::malHash() { }
malHash::malHash(malValueIter argsBegin, malValueIter argsEnd,
                 const String& context)
{
    addToMap(argsBegin, argsEnd, context);
}
malHash::malHash(const Map &map, malValuePtr meta)
: malValue(meta)
, m_map(map)
{

}

malValuePtr
malHash::assoc(malValueIter argsBegin, malValueIter argsEnd) const
{
    auto map = new malHash(m_map);
    map->addToMap(argsBegin, argsEnd, "assoc");
    return malValuePtr(map);
}

bool malHash::contains(malValuePtr key) const
{
    auto it = m_map.find(key);
    return it != m_map.end();
}

malValuePtr
malHash::dissoc(malValueIter argsBegin, malValueIter argsEnd) const
{
    auto map = new malHash(m_map);
    for (auto it = argsBegin; it != argsEnd; ++it) {
        auto key = *it;
        map->m_map.erase(key);
    }
    return malValuePtr(map);
}

malValuePtr malHash::doWithMeta(malValuePtr meta) const
{
    return malValuePtr(new malHash(m_map, meta));
}

malValuePtr malHash::fmap(std::function<malValuePtr(malValuePtr)> f) const
{
    auto map = new malHash();
    for (auto it = m_map.begin(), end = m_map.end(); it != end; ++it) {
        map->m_map[it->first] = f(it->second);
    }
    return malValuePtr(map);
}

malValuePtr malHash::get(malValuePtr key) const
{
    auto it = m_map.find(key);
    return it == m_map.end() ? mal::nilValue() : it->second;
}

malValuePtr malHash::keys() const
{
    auto keys = new malList();
    for (auto it = m_map.begin(), end = m_map.end(); it != end; ++it) {
        keys->push_back(it->first);
    }
    return malValuePtr(keys);
}

malValuePtr malHash::values() const
{
    auto keys = new malList();
    for (auto it = m_map.begin(), end = m_map.end(); it != end; ++it) {
        keys->push_back(it->second);
    }
    return malValuePtr(keys);
}

String malHash::print(bool readably) const
{
    String s = "{";

    auto it = m_map.begin(), end = m_map.end();
    if (it != end) {
        s += it->first->print(readably) + " " + it->second->print(readably);
        ++it;
    }
    for ( ; it != end; ++it) {
        s += " " + it->first->print(readably)
          + " " + it->second->print(readably);
    }

    return s + "}";
}

bool malHash::doIsEqualTo(const malValue* rhs) const
{
    auto r = dynamic_cast<const malHash*>(rhs);
    if (!r) {
        return false;
    }
    const malHash::Map& r_map = r->m_map;
    if (m_map.size() != r_map.size()) {
        return false;
    }

    for (auto it0 = m_map.begin(), end0 = m_map.end(), it1 = r_map.begin();
         it0 != end0; ++it0, ++it1) {

        if (!it0->first->doIsEqualTo(it1->first)) {
            return false;
        }
        if (!it0->second->doIsEqualTo(it1->second)) {
            return false;
        }
    }
    return true;
}

malInteger::malInteger(int64_t value) : m_value(value) { }
bool malInteger::doIsEqualTo(const malValue* rhs) const
{
    auto r = dynamic_cast<const malInteger*>(rhs);
    return r && (m_value == r->m_value);
}
String malInteger::print(bool) const { return std::to_string(m_value); }
int64_t malInteger::value() const { return m_value; }

malStringBase::malStringBase(const String& token) : m_value(token) { }
String malStringBase::print(bool) const { return m_value; }
String malStringBase::value() const { return m_value; }

malKeyword::malKeyword(const String& token) : malStringBase(token) { }
bool malKeyword::doIsEqualTo(const malValue* rhs) const
{
    auto r = dynamic_cast<const malKeyword*>(rhs);
    return r && (value() == r->value());
}

malLambda::malLambda(ApplyFunc apply,
                     const StringVec& bindings,
                     malValuePtr body, malEnvPtr env,
                     bool isMacro,  malValuePtr meta)
: malApplicable(meta)
, m_apply(apply)
, m_bindings(bindings)
, m_body(body)
, m_env(env)
, m_isMacro(isMacro)
{

}

malValuePtr malLambda::apply(malValueIter argsBegin,
                             malValueIter argsEnd) const
{
    return m_apply(argsBegin, argsEnd);
}

StringVec malLambda::getBindings() const { return m_bindings; }

malValuePtr malLambda::asMacro() const
{
    return malValuePtr(new malLambda(m_apply, m_bindings, m_body, m_env,
                                     true));
}

malValuePtr malLambda::doWithMeta(malValuePtr meta) const
{
    return malValuePtr(new malLambda(m_apply, m_bindings, m_body, m_env,
                                     m_isMacro, meta));
}

malEnvPtr malLambda::getEnv() const { return m_env; }
malValuePtr malLambda::getBody() const { return m_body; }
bool malLambda::isMacro() const { return m_isMacro; }
String malLambda::print(bool) const
{
    return STRF("#user-%s(%p)", m_isMacro ? "macro" : "function", this);
}

malList::malList() { }
malList::malList(malValueIter begin, malValueIter end, malValuePtr meta)
: malSequence(begin, end, meta) { }
malValuePtr malList::conj(malValueIter argsBegin,
                          malValueIter argsEnd) const
{
    auto items = new malList();
    while (argsEnd-- != argsBegin) {
        items->push_back(*argsEnd);
    }
    for (auto const &x : *this) {
        items->push_back(x);
    }

    return malValuePtr(items);
}
malValuePtr malList::doWithMeta(malValuePtr meta) const
{
    return malValuePtr(new malList(begin(), end(), meta));
}

String malList::print(bool readably) const
{
    return '(' + printValues(begin(), end(), " ", readably) + ')';
}

malValue::malValue(malValuePtr meta)
: m_meta(meta)
{
}

bool malValue::doIsEqualTo(const malValue*) const { return false; }
malValuePtr malValue::doWithMeta(malValuePtr) const
{
    MAL_FAIL("cannot add metadata to %s", print(true).c_str());
}

bool malValue::isTrue() const
{
    return (this != mal::falseValue())
        && (this != mal::nilValue());
}

malValuePtr malValue::meta() const
{
    return m_meta == NULL ? mal::nilValue() : m_meta;
}

malSequence::malSequence()
{

}
malSequence::malSequence(malValueIter begin, malValueIter end,
                         malValuePtr meta)
: malValue(meta)
, m_items(begin, end)
{

}
malValueIter malSequence::begin() const { return m_items.begin(); }
int malSequence::count() const { return m_items.size(); }

bool malSequence::doIsEqualTo(const malValue* rhs) const
{
    const malSequence* rhsSeq = dynamic_cast<const malSequence*>(rhs);
    if (!rhsSeq) {
        return false;
    }
    if (count() != rhsSeq->count()) {
        return false;
    }

    for (malValueIter it0 = m_items.begin(),
                      it1 = rhsSeq->begin(),
                      end = m_items.end(); it0 != end; ++it0, ++it1) {

        if (!(*it0)->doIsEqualTo((*it1))) {
            return false;
        }
    }
    return true;
}
malValueIter malSequence::end() const { return m_items.end(); }

malValuePtr malSequence::first() const
{
    return count() == 0 ? mal::nilValue() : item(0);
}

String printValues(malValueIter begin, malValueIter end,
                   const String& sep, bool readably)
{
    String str;
    auto it = begin;
    if (it != end) {
        str += (*it)->print(readably);
        ++it;
    }

    for ( ; it != end; ++it) {
        str += sep;
        str += (*it)->print(readably);
    }

    return str;
}
bool malSequence::isEmpty() const { return m_items.empty(); }
malValuePtr malSequence::item(int index) const { return m_items.at(index); }
void malSequence::push_back(malValuePtr newItem) {
    m_items.push_back(newItem);
}

malValuePtr malSequence::rest() const
{
    malValueIter start = (count() > 0) ? begin() + 1 : end();
    return mal::list(start, end());
}

malString::malString(const String& token) : malStringBase(token) { }
bool malString::doIsEqualTo(const malValue* rhs) const
{
    auto r = dynamic_cast<const malString*>(rhs);
    return r && (value() == r->value());
}

String malString::print(bool readably) const
{
    return readably ? escape(value()) : value();
}

malSymbol::malSymbol(const String& token) : malStringBase(token) { }
bool malSymbol::doIsEqualTo(const malValue* rhs) const
{
    auto r = dynamic_cast<const malSymbol*>(rhs);
    return r && (value() == r->value());
}

malVector::malVector() { }
malVector::malVector(malValueIter begin, malValueIter end, malValuePtr meta)
  : malSequence(begin, end, meta) { }
malValuePtr malVector::conj(malValueIter argsBegin,
                            malValueIter argsEnd) const
{
    auto items = new malVector(begin(), end());
    for ( ; argsBegin != argsEnd; ++argsBegin) {
        items->push_back(*argsBegin);
    }
    return malValuePtr(items);
}

malValuePtr malVector::fmap(std::function<malValuePtr(malValuePtr)> f) const
{
    auto items = new malVector();
    for (const auto &x : *this) {
        items->push_back(f(x));
    }
    return malValuePtr(items);
}

malValuePtr malVector::doWithMeta(malValuePtr meta) const
{
    return new malVector(begin(), end(), meta);
}

String malVector::print(bool readably) const
{
    return '[' + printValues(begin(), end(), " ", readably) + ']';
}
