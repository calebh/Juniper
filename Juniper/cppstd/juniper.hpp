#ifndef JUNIPER_H
#define JUNIPER_H

#include <stdlib.h>

namespace juniper
{
    template<typename Result, typename ...Args>
    struct abstract_function
    {
        virtual Result operator()(Args... args) = 0;
        virtual abstract_function *clone() const = 0;
        virtual ~abstract_function() = default;
    };

    template<typename Func, typename Result, typename ...Args>
    class concrete_function : public abstract_function<Result, Args...>
    {
        Func f;
    public:
        concrete_function(const Func &x)
            : f(x)
        {}
        Result operator()(Args... args) override
        {
            return f(args...);
        }
        concrete_function *clone() const override
        {
            return new concrete_function{ f };
        }
    };

    template<typename Func>
    struct func_filter
    {
        typedef Func type;
    };
    template<typename Result, typename ...Args>
    struct func_filter<Result(Args...)>
    {
        typedef Result(*type)(Args...);
    };

    template<typename signature>
    class function;

    template<typename Result, typename ...Args>
    class function<Result(Args...)>
    {
        abstract_function<Result, Args...> *f;
    public:
        function()
            : f(nullptr)
        {}
        template<typename Func> function(const Func &x)
            : f(new concrete_function<typename func_filter<Func>::type, Result, Args...>(x))
        {}
        function(const function &rhs)
            : f(rhs.f ? rhs.f->clone() : nullptr)
        {}
        function &operator=(const function &rhs)
        {
            if ((&rhs != this) && (rhs.f))
            {
                auto *temp = rhs.f->clone();
                delete f;
                f = temp;
            }
            return *this;
        }
        template<typename Func> function &operator=(const Func &x)
        {
            auto *temp = new concrete_function<typename func_filter<Func>::type, Result, Args...>(x);
            delete f;
            f = temp;
            return *this;
        }
        Result operator()(Args... args)
        {
            if (f)
                return (*f)(args...);
            else
                return Result{};
        }
        ~function()
        {
            delete f;
        }
    };

    template <class T>
    void swap(T& a, T& b) {
        T c(a);
        a = b;
        b = c;
    }

    template <typename contained>
    class shared_ptr {
    public:
        shared_ptr() : ptr_(NULL), ref_count_(NULL) { }

        shared_ptr(contained * p)
            : ptr_(p), ref_count_(new int)
        {
            *ref_count_ = 0;
            inc_ref();
        }

        shared_ptr(const shared_ptr& rhs)
            : ptr_(rhs.ptr_), ref_count_(rhs.ref_count_)
        {
            inc_ref();
        }

        ~shared_ptr() {
            if (ref_count_ && 0 == dec_ref()) {
                if (ptr_) {
                    delete ptr_;
                }
                delete ref_count_;
            }
        }

        void set(contained* p) {
          ptr_ = p;
        }

        contained* get() { return ptr_; }
        const contained* get() const { return ptr_; }

        void swap(shared_ptr& rhs) {
            juniper::swap(ptr_, rhs.ptr_);
            juniper::swap(ref_count_, rhs.ref_count_);
        }

        shared_ptr& operator=(const shared_ptr& rhs) {
            shared_ptr tmp(rhs);
            this->swap(tmp);
            return *this;
        }

        //contained& operator*() {
        //    return *ptr_;
        //}

        contained* operator->() {
            return ptr_;
        }

        bool operator==(shared_ptr& rhs) {
            return ptr_ == rhs.ptr_;
        }

        bool operator!=(shared_ptr& rhs) { return !(rhs == *this); }
    private:
        void inc_ref() {
            if (ref_count_) {
                ++(*ref_count_);
            }
        }

        int dec_ref() {
            return --(*ref_count_);
        }

        contained * ptr_;
        int * ref_count_;
    };

    template<typename T, size_t N>
    class array {
    public:
        array<T, N>& fill(T fillWith) {
            for (size_t i = 0; i < N; i++) {
                data[i] = fillWith;
            }

            return *this;
        }

        T& operator[](int i) {
            return data[i];
        }

        bool operator==(array<T, N>& rhs) {
            for (auto i = 0; i < N; i++) {
                if (data[i] != rhs[i]) {
                    return false;
                }
            }
            return true;
        }

        bool operator!=(array<T, N>& rhs) { return !(rhs == *this); }

        T data[N];
    };

    template<typename T>
    T quit() {
        exit(1);
    }
}

#endif
