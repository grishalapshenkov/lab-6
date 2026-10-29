"""
Лабораторная работа № 6. Вариант 14.
Стек и очередь. Исследуемая операция: реализация очереди через два стека.
n = 5000, 10 000, 20 000. Прикладная задача: моделирование потока заявок.
"""
import gc
import json
import math
import random
import statistics
import sys
import time
from collections import deque

SIZES = [5_000, 10_000, 20_000]
REPEATS = 5


# ------------------------------------------------------- односвязный список
class Node:
    """Узел односвязного списка."""
    __slots__ = ("value", "next")

    def __init__(self, value, nxt=None):
        self.value = value
        self.next = nxt


class LinkedList:
    """Односвязный список со ссылкой на хвост."""

    def __init__(self):
        self.head = None
        self.tail = None
        self.size = 0

    def push_front(self, value):
        self.head = Node(value, self.head)
        if self.tail is None:
            self.tail = self.head
        self.size += 1

    def push_back(self, value):
        node = Node(value)
        if self.tail is None:
            self.head = self.tail = node
        else:
            self.tail.next = node
            self.tail = node
        self.size += 1

    def insert(self, index, value):
        """Вставка перед элементом с номером index — Θ(index)."""
        if not 0 <= index <= self.size:
            raise IndexError("Индекс вне диапазона")
        if index == 0:
            return self.push_front(value)
        if index == self.size:
            return self.push_back(value)
        prev = self.head
        for _ in range(index - 1):
            prev = prev.next
        prev.next = Node(value, prev.next)
        self.size += 1

    def pop_front(self):
        if self.head is None:
            raise IndexError("Список пуст")
        value = self.head.value
        self.head = self.head.next
        if self.head is None:
            self.tail = None
        self.size -= 1
        return value

    def get(self, index):
        if not 0 <= index < self.size:
            raise IndexError("Индекс вне диапазона")
        node = self.head
        for _ in range(index):
            node = node.next
        return node.value

    def find(self, value):
        """Индекс первого вхождения значения или -1 — Θ(n)."""
        node, i = self.head, 0
        while node:
            if node.value == value:
                return i
            node, i = node.next, i + 1
        return -1

    def to_list(self):
        result, node = [], self.head
        while node:
            result.append(node.value)
            node = node.next
        return result

    def __len__(self):
        return self.size


# ------------------------------------------------------------------ стеки
class ArrayStack:
    """Стек на динамическом массиве (list). Счётчик ops — число операций push/pop."""

    def __init__(self):
        self.data = []
        self.ops = 0

    def push(self, value):
        self.ops += 1
        self.data.append(value)

    def pop(self):
        if not self.data:
            raise IndexError("Стек пуст")
        self.ops += 1
        return self.data.pop()

    def top(self):
        if not self.data:
            raise IndexError("Стек пуст")
        return self.data[-1]

    def __len__(self):
        return len(self.data)

    def __bool__(self):
        return bool(self.data)


class LinkedStack:
    """Стек на односвязном списке: вершина — голова списка."""

    def __init__(self):
        self.lst = LinkedList()
        self.ops = 0

    def push(self, value):
        self.ops += 1
        self.lst.push_front(value)

    def pop(self):
        self.ops += 1
        return self.lst.pop_front()

    def top(self):
        return self.lst.get(0)

    def __len__(self):
        return len(self.lst)

    def __bool__(self):
        return len(self.lst) > 0


# ---------------------------------------------------------------- очереди
class TwoStackQueue:
    """Очередь на двух стеках: вход (inbox) и выход (outbox).
    Элементы перекладываются из inbox в outbox только когда outbox пуст,
    поэтому каждый элемент перекладывается не более одного раза."""

    def __init__(self, stack_cls=ArrayStack):
        self.inbox, self.outbox = stack_cls(), stack_cls()

    def enqueue(self, value):
        self.inbox.push(value)                       # Θ(1)

    def _transfer(self):
        while self.inbox:
            self.outbox.push(self.inbox.pop())

    def dequeue(self):
        if not self.outbox:
            if not self.inbox:
                raise IndexError("Очередь пуста")
            self._transfer()                         # Θ(n) в худшем случае
        return self.outbox.pop()

    def front(self):
        if not self.outbox:
            self._transfer()
        return self.outbox.top()

    def stack_ops(self):
        return self.inbox.ops + self.outbox.ops

    def __len__(self):
        return len(self.inbox) + len(self.outbox)


class NaiveTwoStackQueue:
    """Неудачный вариант: при каждом извлечении все элементы переносятся
    во второй стек и обратно — Θ(n) на каждую операцию dequeue."""

    def __init__(self, stack_cls=ArrayStack):
        self.main, self.aux = stack_cls(), stack_cls()

    def enqueue(self, value):
        self.main.push(value)

    def dequeue(self):
        if not self.main:
            raise IndexError("Очередь пуста")
        while self.main:
            self.aux.push(self.main.pop())
        value = self.aux.pop()
        while self.aux:
            self.main.push(self.aux.pop())
        return value

    def stack_ops(self):
        return self.main.ops + self.aux.ops

    def __len__(self):
        return len(self.main)


class CircularQueue:
    """Очередь на кольцевом буфере фиксированной ёмкости."""

    def __init__(self, capacity):
        self.data = [None] * capacity
        self.capacity = capacity
        self.head = 0
        self.count = 0

    def enqueue(self, value):
        if self.count == self.capacity:
            raise OverflowError("Очередь переполнена")
        self.data[(self.head + self.count) % self.capacity] = value
        self.count += 1

    def dequeue(self):
        if self.count == 0:
            raise IndexError("Очередь пуста")
        value = self.data[self.head]
        self.data[self.head] = None
        self.head = (self.head + 1) % self.capacity
        self.count -= 1
        return value

    def __len__(self):
        return self.count


class ListQueue:
    """Очередь на встроенном list: извлечение из начала — pop(0), Θ(n)."""

    def __init__(self):
        self.data = []

    def enqueue(self, value):
        self.data.append(value)

    def dequeue(self):
        return self.data.pop(0)

    def __len__(self):
        return len(self.data)


# ---------------------------------------------- Т1: проверка на малом примере
def demo():
    """Работа очереди на двух стеках на малом примере (вывод после каждой операции)."""
    q = TwoStackQueue()
    script = [("enq", 1), ("enq", 2), ("enq", 3), ("deq", None), ("enq", 4),
              ("deq", None), ("deq", None), ("enq", 5), ("deq", None),
              ("deq", None), ("deq", None)]
    lines = []
    for op, v in script:
        if op == "enq":
            q.enqueue(v)
            title = f"enqueue({v})"
            result = ""
        else:
            title = "dequeue()"
            try:
                result = f" -> {q.dequeue()}"
            except IndexError:
                result = " -> ошибка: очередь пуста"
        lines.append(f"{title + result:<28} inbox={q.inbox.data}  outbox={q.outbox.data}")
    return lines


def self_test():
    """Сверка всех очередей с эталоном deque на случайной последовательности операций."""
    rng = random.Random(3)
    for make in (TwoStackQueue, lambda: TwoStackQueue(LinkedStack),
                 NaiveTwoStackQueue, lambda: CircularQueue(1000), ListQueue):
        q, ref = make(), deque()
        for i in range(5000):
            if ref and rng.random() < 0.45:
                assert q.dequeue() == ref.popleft()
            elif len(ref) < 900:
                q.enqueue(i)
                ref.append(i)
        assert len(q) == len(ref)
    print("Самопроверка пройдена: порядок FIFO совпадает с collections.deque.")


# ------------------------------------------------------------------ замеры
def best_median(action, repeats=REPEATS):
    times = []
    for _ in range(repeats):
        gc.collect()
        t0 = time.perf_counter()
        action()
        times.append(time.perf_counter() - t0)
    return statistics.median(times)


def filled(make, n):
    q = make()
    for i in range(n):
        q.enqueue(i)
    return q


def measure_queues(n):
    """Время n постановок и n извлечений для каждой реализации, с."""
    makers = {"два стека": TwoStackQueue,
              "кольцевой буфер": lambda: CircularQueue(n),
              "list (append / pop(0))": ListQueue}
    out = {}
    for name, make in makers.items():
        def enq(make=make):
            q = make()
            for i in range(n):
                q.enqueue(i)

        def deq(make=make):
            q = filled(make, n)
            t0 = time.perf_counter()
            for _ in range(n):
                q.dequeue()
            return time.perf_counter() - t0

        t_enq = best_median(enq)
        t_deq = statistics.median(deq() for _ in range(REPEATS))
        out[name] = {"enqueue": t_enq, "dequeue": t_deq}
    return out


def measure_naive(n, pairs=100):
    """Время одной пары dequeue+enqueue при длине очереди n (после первого переноса), с."""
    def run(make):
        q = filled(make, n)
        q.dequeue()                  # прогрев: первое извлечение выполняет перенос
        q.enqueue(-1)
        t0 = time.perf_counter()
        for i in range(pairs):
            q.dequeue()
            q.enqueue(i)
        return (time.perf_counter() - t0) / pairs
    return {"наивный перенос": statistics.median(run(NaiveTwoStackQueue) for _ in range(3)),
            "два стека": statistics.median(run(TwoStackQueue) for _ in range(3))}


def dequeue_spike(n):
    """Время каждого из n извлечений из очереди на двух стеках, с."""
    q = filled(TwoStackQueue, n)
    times = []
    for _ in range(n):
        t0 = time.perf_counter()
        q.dequeue()
        times.append(time.perf_counter() - t0)
    return times


def count_stack_ops(n):
    """Стековых операций на элемент после n постановок и n извлечений."""
    q = filled(TwoStackQueue, n)
    for _ in range(n):
        q.dequeue()
    return q.stack_ops() / n


def memory_report(n=10_000):
    """Т4: оценка памяти контейнеров на n элементах (sys.getsizeof, байт)."""
    arr = []
    for i in range(n):
        arr.append(i)
    exact = list(range(n))
    ll = LinkedList()
    for i in range(n):
        ll.push_back(i)
    nodes, node = 0, ll.head
    while node:
        nodes += sys.getsizeof(node)
        node = node.next

    class DictNode:                          # узел без __slots__ (для сравнения)
        def __init__(self, value, nxt=None):
            self.value, self.next = value, nxt
    dn = DictNode(0)
    dict_node = sys.getsizeof(dn) + sys.getsizeof(dn.__dict__)
    q = filled(TwoStackQueue, n)
    q.dequeue()                              # перекладываем всё во второй стек
    return {
        "n": n,
        "list_append": sys.getsizeof(arr),
        "list_exact": sys.getsizeof(exact),
        "linked": sys.getsizeof(ll) + nodes,
        "node": sys.getsizeof(ll.head),
        "node_dict": dict_node,
        "two_stack": sum(sys.getsizeof(s.data) for s in (q.inbox, q.outbox)),
        "deque": sys.getsizeof(deque(range(n))),
        "int_obj": sys.getsizeof(n),
    }


# --------------------------------------------- прикладная задача: поток заявок
def simulate(num_requests, lam, mu, seed, queue_factory=TwoStackQueue):
    """Система массового обслуживания M/M/1: один обработчик, очередь FIFO.
    Заявки поступают с интенсивностью lam, обслуживаются с интенсивностью mu.
    Возвращает среднее время ожидания в очереди, среднюю длину очереди,
    максимальную длину очереди и признак соблюдения FIFO."""
    rng = random.Random(seed)
    queue = queue_factory()
    t, server_free_at, next_id, served_id = 0.0, 0.0, 0, -1
    arrival_time = {}
    arrivals, waits, area, max_len, last_t, fifo_ok = [], [], 0.0, 0, 0.0, True
    for _ in range(num_requests):
        t += rng.expovariate(lam)
        arrivals.append(t)
    i = 0
    # дискретно-событийное моделирование
    while i < num_requests or len(queue):
        next_arrival = arrivals[i] if i < num_requests else math.inf
        if len(queue) and server_free_at <= next_arrival:
            now = max(server_free_at, last_t)
            area += len(queue) * (now - last_t)
            last_t = now
            req = queue.dequeue()
            fifo_ok &= (req > served_id)
            served_id = req
            waits.append(now - arrival_time.pop(req))
            server_free_at = now + rng.expovariate(mu)
        else:
            area += len(queue) * (next_arrival - last_t)
            last_t = next_arrival
            queue.enqueue(next_id)
            arrival_time[next_id] = next_arrival
            next_id += 1
            i += 1
            max_len = max(max_len, len(queue))
            if server_free_at < next_arrival and len(queue) == 1:
                server_free_at = next_arrival
    return {"wait": statistics.mean(waits), "avg_len": area / last_t,
            "max_len": max_len, "fifo": fifo_ok, "served": len(waits), "waits": waits}


# ----------------------------------------------------------------- графики
def make_plots(res):
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    ns = [r["n"] for r in res["queues"]]

    fig, axes = plt.subplots(1, 2, figsize=(11, 4.3))
    for ax, op, title in ((axes[0], "enqueue", "n постановок в очередь"),
                          (axes[1], "dequeue", "n извлечений из очереди")):
        for name in res["queues"][0]["t"]:
            ax.plot(ns, [r["t"][name][op] * 1e3 for r in res["queues"]], "o-", label=name)
        ax.set_xscale("log"); ax.set_yscale("log")
        ax.set_xlabel("n"); ax.set_ylabel("время, мс"); ax.set_title(title)
        ax.grid(True, which="both", alpha=.3); ax.legend(fontsize=8)
    plt.tight_layout(); plt.savefig("img/lr6_time.png", dpi=170); plt.close()

    sp = res["spike"]
    plt.figure(figsize=(6.8, 4.2))
    plt.semilogy(range(1, len(sp) + 1), [t * 1e6 for t in sp], ".", ms=2)
    plt.xlabel("номер операции dequeue"); plt.ylabel("время одной операции, мкс")
    plt.title(f"Очередь на двух стеках: время каждого извлечения (n = {len(sp):,})".replace(",", " "))
    plt.grid(True, which="both", alpha=.3)
    plt.tight_layout(); plt.savefig("img/lr6_spike.png", dpi=170); plt.close()

    plt.figure(figsize=(6.8, 4.2))
    for name in ("наивный перенос", "два стека"):
        plt.plot(ns, [r["naive"][name] * 1e6 for r in res["queues"]], "o-", label=name)
    plt.yscale("log"); plt.xscale("log")
    plt.xlabel("длина очереди n"); plt.ylabel("время пары dequeue + enqueue, мкс")
    plt.title("Наивный перенос и перенос по требованию")
    plt.grid(True, which="both", alpha=.3); plt.legend()
    plt.tight_layout(); plt.savefig("img/lr6_naive.png", dpi=170); plt.close()

    sim = res["sim_trace"]
    fig, axes = plt.subplots(1, 2, figsize=(11, 3.8))
    axes[0].plot(sim["len_t"], sim["len_v"], lw=.6)
    axes[0].set_xlabel("номер события"); axes[0].set_ylabel("длина очереди")
    axes[0].set_title("Длина очереди заявок (ρ = 0,8)")
    axes[1].hist(sim["waits"], bins=50, color="#55a868")
    axes[1].set_xlabel("время ожидания в очереди"); axes[1].set_ylabel("число заявок")
    axes[1].set_title("Распределение времени ожидания")
    for ax in axes:
        ax.grid(True, alpha=.3)
    plt.tight_layout(); plt.savefig("img/lr6_sim.png", dpi=170); plt.close()


# -------------------------------------------------------------------- main
if __name__ == "__main__":
    self_test()
    res = {"demo": demo()}
    print("\n".join(res["demo"]))

    res["queues"] = []
    for n in SIZES:
        t = measure_queues(n)
        naive = measure_naive(n)
        res["queues"].append({"n": n, "t": t, "naive": naive, "ops_per_item": count_stack_ops(n)})
        print(f"n = {n}: " + "; ".join(f"{k}: {v['enqueue']:.5f}/{v['dequeue']:.5f}" for k, v in t.items()),
              "| naive", {k: round(v * 1e6, 1) for k, v in naive.items()}, flush=True)

    spike = dequeue_spike(SIZES[-1])
    res["spike"] = spike
    print(f"извлечение: первое {spike[0] * 1e6:.1f} мкс, медиана остальных "
          f"{statistics.median(spike[1:]) * 1e6:.2f} мкс, среднее {statistics.mean(spike) * 1e6:.2f} мкс")

    res["memory"] = memory_report(10_000)
    print(res["memory"])

    # прикладная задача: M/M/1, lam = 0.8, mu = 1.0 (ρ = 0.8)
    lam, mu = 0.8, 1.0
    rho = lam / mu
    res["sim_theory"] = {"lam": lam, "mu": mu, "rho": rho, "wq": rho / (mu - lam),
                         "lq": rho ** 2 / (1 - rho)}
    res["sim"] = []
    for n in SIZES:
        reps = [simulate(n, lam, mu, seed) for seed in range(30)]
        res["sim"].append({"n": n,
                           "wait_mean": statistics.mean(r["wait"] for r in reps),
                           "wait_sd": statistics.stdev(r["wait"] for r in reps),
                           "len_mean": statistics.mean(r["avg_len"] for r in reps),
                           "len_sd": statistics.stdev(r["avg_len"] for r in reps),
                           "max_len": statistics.mean(r["max_len"] for r in reps),
                           "fifo": all(r["fifo"] for r in reps),
                           "served": min(r["served"] for r in reps)})
        print(res["sim"][-1])
    # идентичность результатов для разных реализаций очереди при одинаковых случайных числах

    class DequeQueue:
        def __init__(self):
            self.d = deque()

        def enqueue(self, v):
            self.d.append(v)

        def dequeue(self):
            return self.d.popleft()

        def __len__(self):
            return len(self.d)
    a = simulate(5000, lam, mu, 0)
    b = simulate(5000, lam, mu, 0, DequeQueue)
    res["sim_same"] = (a["wait"] == b["wait"] and a["avg_len"] == b["avg_len"])
    print("совпадение с deque:", res["sim_same"])

    # трасса одного прогона для графиков
    lens = []

    class TraceQueue(TwoStackQueue):
        def enqueue(self, v):
            super().enqueue(v)
            lens.append(len(self))

        def dequeue(self):
            r = super().dequeue()
            lens.append(len(self))
            return r
    trace = simulate(5000, lam, mu, 1, TraceQueue)
    res["sim_trace"] = {"len_t": list(range(len(lens))), "len_v": lens, "waits": trace["waits"]}
    with open("res/lr6.json", "w", encoding="utf-8") as f:
        json.dump(res, f, ensure_ascii=False)
    make_plots(res)
