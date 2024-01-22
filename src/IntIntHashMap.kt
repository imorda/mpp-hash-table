import kotlinx.atomicfu.AtomicIntArray
import kotlinx.atomicfu.AtomicRef
import kotlinx.atomicfu.atomic
import kotlin.math.absoluteValue

/**
 * @author Belousov Timofey
 */

/**
 * Int-to-Int hash map with open addressing and linear probes.
 */
class IntIntHashMap {
    private val core = atomic(Core(INITIAL_CAPACITY))

    /**
     * Returns value for the corresponding key or zero if this key is not present.
     *
     * @param key a positive key.
     * @return value for the corresponding or zero if this key is not present.
     * @throws IllegalArgumentException if key is not positive.
     */
    operator fun get(key: Int): Int {
        require(key > 0) { "Key must be positive: $key" }
        return toValue(core.value.getInternal(key))
    }

    /**
     * Changes value for the corresponding key and returns old value or zero if key was not present.
     *
     * @param key   a positive key.
     * @param value a positive value.
     * @return old value or zero if this key was not present.
     * @throws IllegalArgumentException if key or value are not positive, or value is equal to
     * [Integer.MAX_VALUE] which is reserved.
     */
    fun put(key: Int, value: Int): Int {
        require(key > 0) { "Key must be positive: $key" }
        require(isValue(value)) { "Invalid value: $value" }
        return toValue(putAndRehashWhileNeeded(key, value))
    }

    /**
     * Removes value for the corresponding key and returns old value or zero if key was not present.
     *
     * @param key a positive key.
     * @return old value or zero if this key was not present.
     * @throws IllegalArgumentException if key is not positive.
     */
    fun remove(key: Int): Int {
        require(key > 0) { "Key must be positive: $key" }
        return toValue(putAndRehashWhileNeeded(key, DEL_VALUE))
    }

    private fun putAndRehashWhileNeeded(key: Int, value: Int): Int {
        while (true) {
            val oldCore = core.value
            val oldValue = oldCore.putInternal(key, value)
            if (oldValue != NEEDS_REHASH) return oldValue
            val newCore = oldCore.rehash()
            while (true) {
                val curCore = core.value
                if (curCore.capacity < newCore.capacity) {
                    if (!core.compareAndSet(curCore, newCore)) continue
                }
                break
            }
        }
    }

    private class Core(val capacity: Int) {
        // Pairs of <key, value> here, the actual
        // size of the map is twice as big.
        val map = AtomicIntArray(2 * capacity)
        val shift: Int
        val next: AtomicRef<Core?> = atomic(null)

        init {
            val mask = capacity - 1
            assert(mask > 0 && mask and capacity == 0) { "Capacity must be power of 2: $capacity" }
            shift = 32 - Integer.bitCount(mask)
        }

        fun getInternal(key: Int): Int {
            var index = index(key)
            var probes = 0

            while (true) {
                val curKey = map[index].value
                if (curKey == key) break

                if (curKey == NULL_KEY) return NULL_VALUE
                if (++probes >= MAX_PROBES) return NULL_VALUE
                if (index == 0) index = map.size
                index -= 2
            }

            // found key -- return value
            while (true) {
                val curValue = map[index + 1].value

                if (curValue == STOLEN_VALUE) return getNextCore().getInternal(key)
                if (curValue < 0) {
                    completeCopy(index)
                    continue
                }

                return curValue
            }
        }

        fun putInternal(key: Int, value: Int): Int {
            var index = index(key)
            var probes = 0

            while (true) {
                val curKey = map[index].value
                if (curKey == key) break

                if (curKey == NULL_KEY) {
                    // not found -- claim this slot
                    if (value == DEL_VALUE) return NULL_VALUE // remove of missing item, no need to claim slot
                    if (!map[index].compareAndSet(curKey, key)) continue
                    break
                }

                if (++probes >= MAX_PROBES) return NEEDS_REHASH
                if (index == 0) index = map.size
                index -= 2
            }

            // found key -- update value
            while (true) {
                val curValue = map[index + 1].value

                if (curValue == STOLEN_VALUE) return getNextCore().putInternal(key, value)
                if (curValue < 0) {
                    completeCopy(index)
                    continue
                }

                if (map[index + 1].compareAndSet(curValue, value)) return curValue
            }
        }

        private fun completeCopy(oldIndex: Int) {
            val keyToCopy = map[oldIndex].value
            val frozenVal = map[oldIndex + 1].value
            require(keyToCopy > 0) { "WTF? $keyToCopy $frozenVal" }
            require(frozenVal < 0) { "WTF?" }

            if (frozenVal == STOLEN_VALUE) {
                return
            }
            val valToCopy = frozenVal.absoluteValue

            var newCore = getNextCore()

            // claim new slot
            var index: Int
            claimed@ while (true) {
                index = newCore.index(keyToCopy)
                var probes = 0
                while (true) {
                    val curKey = newCore.map[index].value
                    if (curKey == keyToCopy) break@claimed

                    if (curKey == NULL_KEY) {
                        // not found -- claim this slot
                        if (valToCopy == DEL_VALUE) throw IllegalStateException("WTF??")
                        if (!newCore.map[index].compareAndSet(curKey, keyToCopy)) continue
                        break@claimed
                    }

                    if (++probes >= MAX_PROBES) break
                    if (index == 0) index = newCore.map.size
                    index -= 2
                }

                newCore = newCore.rehash()
            }

            // copy the value
            newCore.map[index + 1].compareAndSet(0, valToCopy)

            // mark as stolen
            this.map[oldIndex + 1].compareAndSet(frozenVal, STOLEN_VALUE)
        }

        private fun getNextCore(): Core {
            val curNext = next.value
            if (curNext != null) return curNext

            val newNext = Core(map.size) // map.length is twice the current capacity

            return if (next.compareAndSet(null, newNext)) {
                newNext
            } else {
                next.value!!
            }
        }

        fun rehash(): Core {
            var index = 0
            val newCore = getNextCore()

            while (index < map.size) {
                val curValue = map[index + 1].value
                if (isValue(curValue)) {
                    if (!map[index + 1].compareAndSet(curValue, -curValue)) continue
                    completeCopy(index)
                } else if (curValue < 0 && curValue != STOLEN_VALUE) {
                    completeCopy(index)
                } else if (curValue == 0 || curValue == DEL_VALUE) {
                    if (!map[index + 1].compareAndSet(curValue, STOLEN_VALUE)) continue
                }
                index += 2
            }
            return newCore
        }

        /**
         * Returns an initial index in map to look for a given key.
         */
        fun index(key: Int): Int = (key * MAGIC ushr shift) * 2
    }
}

private const val MAGIC = -0x61c88647 // golden ratio
private const val INITIAL_CAPACITY = 2 // !!! DO NOT CHANGE INITIAL CAPACITY !!!
private const val MAX_PROBES = 8 // max number of probes to find an item
private const val NULL_KEY = 0 // missing key (initial value)
private const val NULL_VALUE = 0 // missing value (initial value)
private const val DEL_VALUE = Int.MAX_VALUE // mark for removed value
private const val NEEDS_REHASH = -1 // returned by `putInternal` to indicate that rehash is needed
private const val STOLEN_VALUE = Int.MIN_VALUE
// negative values are meant to be copied to the next core

// Checks is the value is in the range of allowed values
private fun isValue(value: Int): Boolean = value in (1 until DEL_VALUE)

// Converts internal value to the public results of the methods
private fun toValue(value: Int): Int = if (isValue(value)) value else 0