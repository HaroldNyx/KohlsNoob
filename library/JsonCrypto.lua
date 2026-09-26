local HttpService = game:GetService("HttpService")

local JsonCrypto = {}

-- ===================== bit helpers =====================

local function add32(a, b)
	return bit32.band(a + b, 0xFFFFFFFF)
end

local function rotl32(x, n)
	return bit32.bor(bit32.lshift(x, n), bit32.rshift(x, 32 - n))
end

-- ===================== byte <-> word helpers =====================

local function bytesToWords(bytes, startIndex, count)
	local words = {}
	for i = 0, count - 1 do
		local b0 = bytes[startIndex + i * 4] or 0
		local b1 = bytes[startIndex + i * 4 + 1] or 0
		local b2 = bytes[startIndex + i * 4 + 2] or 0
		local b3 = bytes[startIndex + i * 4 + 3] or 0
		words[i + 1] = bit32.bor(b0, bit32.lshift(b1, 8), bit32.lshift(b2, 16), bit32.lshift(b3, 24))
	end
	return words
end

local function wordsToBytes(words, count)
	local bytes = {}
	for i = 1, count do
		local w = words[i]
		bytes[#bytes + 1] = bit32.band(w, 0xFF)
		bytes[#bytes + 1] = bit32.band(bit32.rshift(w, 8), 0xFF)
		bytes[#bytes + 1] = bit32.band(bit32.rshift(w, 16), 0xFF)
		bytes[#bytes + 1] = bit32.band(bit32.rshift(w, 24), 0xFF)
	end
	return bytes
end

local function stringToBytes(s)
	local bytes = {}
	for i = 1, #s do
		bytes[i] = string.byte(s, i)
	end
	return bytes
end

local function bytesToString(bytes)
	local chars = {}
	for i = 1, #bytes do
		chars[i] = string.char(bytes[i])
	end
	return table.concat(chars)
end

-- ===================== ChaCha20 core =====================

local CONSTANTS = { 0x61707865, 0x3320646e, 0x79622d32, 0x6b206574 }

local function quarterRound(state, a, b, c, d)
	state[a] = add32(state[a], state[b]); state[d] = bit32.bxor(state[d], state[a]); state[d] = rotl32(state[d], 16)
	state[c] = add32(state[c], state[d]); state[b] = bit32.bxor(state[b], state[c]); state[b] = rotl32(state[b], 12)
	state[a] = add32(state[a], state[b]); state[d] = bit32.bxor(state[d], state[a]); state[d] = rotl32(state[d], 8)
	state[c] = add32(state[c], state[d]); state[b] = bit32.bxor(state[b], state[c]); state[b] = rotl32(state[b], 7)
end

-- key: 8 words (256-bit), nonce: 3 words (96-bit), counter: 1 word
local function chacha20Block(key, counter, nonce)
	local init = {}
	for i = 1, 4 do init[i] = CONSTANTS[i] end
	for i = 1, 8 do init[4 + i] = key[i] end
	init[13] = counter
	for i = 1, 3 do init[13 + i] = nonce[i] end

	local working = table.clone(init)

	for _ = 1, 10 do
		-- column rounds
		quarterRound(working, 1, 5, 9, 13)
		quarterRound(working, 2, 6, 10, 14)
		quarterRound(working, 3, 7, 11, 15)
		quarterRound(working, 4, 8, 12, 16)
		-- diagonal rounds
		quarterRound(working, 1, 6, 11, 16)
		quarterRound(working, 2, 7, 12, 13)
		quarterRound(working, 3, 8, 9, 14)
		quarterRound(working, 4, 5, 10, 15)
	end

	for i = 1, 16 do
		working[i] = add32(working[i], init[i])
	end

	return wordsToBytes(working, 16)
end

-- XOR `bytes` with the ChaCha20 keystream; same function encrypts and decrypts
local function chacha20Xor(bytes, key, nonce)
	local out = {}
	local counter = 1
	local pos = 1
	local total = #bytes

	while pos <= total do
		local keystream = chacha20Block(key, counter, nonce)
		for i = 1, 64 do
			if pos > total then break end
			out[pos] = bit32.bxor(bytes[pos], keystream[i])
			pos = pos + 1
		end
		counter = counter + 1
	end

	return out
end

-- ===================== base64 (for safe storage/transport as text) =====================

local B64_CHARS = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/"

local function base64Encode(bytes)
	local out = {}
	local len = #bytes
	local i = 1
	while i <= len do
		local b1, b2, b3 = bytes[i], bytes[i + 1], bytes[i + 2]
		local n = bit32.lshift(b1, 16) + bit32.lshift(b2 or 0, 8) + (b3 or 0)
		local c1 = bit32.rshift(n, 18) % 64
		local c2 = bit32.rshift(n, 12) % 64
		local c3 = bit32.rshift(n, 6) % 64
		local c4 = n % 64
		out[#out + 1] = string.sub(B64_CHARS, c1 + 1, c1 + 1)
		out[#out + 1] = string.sub(B64_CHARS, c2 + 1, c2 + 1)
		out[#out + 1] = b2 and string.sub(B64_CHARS, c3 + 1, c3 + 1) or "="
		out[#out + 1] = b3 and string.sub(B64_CHARS, c4 + 1, c4 + 1) or "="
		i = i + 3
	end
	return table.concat(out)
end

local B64_LOOKUP = {}
for i = 1, #B64_CHARS do
	B64_LOOKUP[string.sub(B64_CHARS, i, i)] = i - 1
end

local function base64Decode(str)
	str = string.gsub(str, "[^%w%+%/]", "")
	local bytes = {}
	local i = 1
	local len = #str
	while i <= len do
		local c1 = B64_LOOKUP[string.sub(str, i, i)] or 0
		local c2 = B64_LOOKUP[string.sub(str, i + 1, i + 1)] or 0
		local c3 = B64_LOOKUP[string.sub(str, i + 2, i + 2)]
		local c4 = B64_LOOKUP[string.sub(str, i + 3, i + 3)]
		local n = bit32.lshift(c1, 18) + bit32.lshift(c2, 12) + bit32.lshift(c3 or 0, 6) + (c4 or 0)
		bytes[#bytes + 1] = bit32.band(bit32.rshift(n, 16), 0xFF)
		if c3 then bytes[#bytes + 1] = bit32.band(bit32.rshift(n, 8), 0xFF) end
		if c4 then bytes[#bytes + 1] = bit32.band(n, 0xFF) end
		i = i + 4
	end
	return bytes
end

-- ===================== hex helpers (copy-paste-safe key format) =====================

local function bytesToHex(bytes)
	local out = {}
	for i = 1, #bytes do
		out[i] = string.format("%02x", bytes[i])
	end
	return table.concat(out)
end

local function hexToBytes(hex)
	hex = string.gsub(hex, "%s+", "") -- tolerate stray whitespace/newlines from pasting
	local bytes = {}
	for i = 1, #hex, 2 do
		bytes[#bytes + 1] = tonumber(string.sub(hex, i, i + 1), 16)
	end
	return bytes
end

-- ===================== Roblox data type support =====================
-- HttpService:JSONEncode errors on Vector3/CFrame/etc, so we walk the table
-- beforehand and swap each supported type for a plain {__rtype=..., d={...}}
-- table, then reverse it after decoding. Add an entry to both tables to
-- support more types.

local ROBLOX_ENCODERS = {
	Vector3 = function(v) return { X = v.X, Y = v.Y, Z = v.Z } end,
	Vector2 = function(v) return { X = v.X, Y = v.Y } end,
	CFrame = function(v) return { table.unpack({ v:GetComponents() }) } end,
	Color3 = function(v) return { R = v.R, G = v.G, B = v.B } end,
	UDim = function(v) return { Scale = v.Scale, Offset = v.Offset } end,
	UDim2 = function(v)
		return { XScale = v.X.Scale, XOffset = v.X.Offset, YScale = v.Y.Scale, YOffset = v.Y.Offset }
	end,
	BrickColor = function(v) return { Number = v.Number } end,
	EnumItem = function(v) return { EnumType = tostring(v.EnumType), Name = v.Name } end,
	NumberRange = function(v) return { Min = v.Min, Max = v.Max } end,
}

local ROBLOX_DECODERS = {
	Vector3 = function(d) return Vector3.new(d.X, d.Y, d.Z) end,
	Vector2 = function(d) return Vector2.new(d.X, d.Y) end,
	CFrame = function(d) return CFrame.new(table.unpack(d)) end,
	Color3 = function(d) return Color3.new(d.R, d.G, d.B) end,
	UDim = function(d) return UDim.new(d.Scale, d.Offset) end,
	UDim2 = function(d) return UDim2.new(d.XScale, d.XOffset, d.YScale, d.YOffset) end,
	BrickColor = function(d) return BrickColor.new(d.Number) end,
	EnumItem = function(d) return Enum[d.EnumType][d.Name] end,
	NumberRange = function(d) return NumberRange.new(d.Min, d.Max) end,
}

-- Recursively replaces Roblox-typed values with plain JSON-safe tables.
local function encodeRobloxTypes(value)
	local kind = typeof(value)
	local encoder = ROBLOX_ENCODERS[kind]
	if encoder then
		return { __rtype = kind, d = encoder(value) }
	elseif kind == "table" then
		local out = {}
		for k, v in pairs(value) do
			out[k] = encodeRobloxTypes(v)
		end
		return out
	else
		-- numbers, strings, booleans, nil pass through unchanged
		return value
	end
end

-- Recursively restores {__rtype=..., d=...} markers back into real Roblox types.
local function decodeRobloxTypes(value)
	if type(value) == "table" then
		if value.__rtype and ROBLOX_DECODERS[value.__rtype] then
			return ROBLOX_DECODERS[value.__rtype](value.d)
		end
		local out = {}
		for k, v in pairs(value) do
			out[k] = decodeRobloxTypes(v)
		end
		return out
	else
		return value
	end
end

-- ===================== public API =====================

-- Generates a fresh 256-bit key as a 64-character hex string, e.g.
-- "a3f9c1...". This is plain printable text, so it's safe to copy-paste
-- into chat, a notes file, or a server-side constant.
-- Generate this ONCE (e.g. print it from a throwaway Studio script), then
-- store the resulting string in server-side code only — never in a LocalScript.
function JsonCrypto.newKey()
	local rng = Random.new(os.clock() * 1e6 + os.time())
	local bytes = {}
	for i = 1, 32 do
		bytes[i] = rng:NextInteger(0, 255)
	end
	return bytesToHex(bytes)
end

-- Encrypts a Lua table (or any JSON-encodable value) into a base64 string.
-- The 12-byte random nonce is generated per call and stored alongside the
-- ciphertext, so the same key can safely be reused across many messages.
function JsonCrypto.encryptJSON(data, keyHex)
	local keyBytes = hexToBytes(keyHex)
	assert(#keyBytes == 32, "key must decode to exactly 32 bytes; generate one with JsonCrypto.newKey()")

	local json = HttpService:JSONEncode(encodeRobloxTypes(data))
	local plainBytes = stringToBytes(json)

	local keyWords = bytesToWords(keyBytes, 1, 8)

	local rng = Random.new(os.clock() * 1e6 + os.time())
	local nonceBytes = {}
	for i = 1, 12 do
		nonceBytes[i] = rng:NextInteger(0, 255)
	end
	local nonceWords = bytesToWords(nonceBytes, 1, 3)

	local cipherBytes = chacha20Xor(plainBytes, keyWords, nonceWords)

	-- prepend the nonce so decryption can recover it
	local combined = {}
	for i = 1, 12 do combined[i] = nonceBytes[i] end
	for i = 1, #cipherBytes do combined[12 + i] = cipherBytes[i] end

	return base64Encode(combined)
end

-- Decrypts a base64 string produced by encryptJSON back into a Lua table.
function JsonCrypto.decryptJSON(packedString, keyHex)
	local keyBytes = hexToBytes(keyHex)
	assert(#keyBytes == 32, "key must decode to exactly 32 bytes")

	local combined = base64Decode(packedString)

	local nonceBytes = {}
	for i = 1, 12 do nonceBytes[i] = combined[i] end
	local nonceWords = bytesToWords(nonceBytes, 1, 3)

	local cipherBytes = {}
	for i = 13, #combined do cipherBytes[i - 12] = combined[i] end

	local keyWords = bytesToWords(keyBytes, 1, 8)

	local plainBytes = chacha20Xor(cipherBytes, keyWords, nonceWords)
	local json = bytesToString(plainBytes)

	return decodeRobloxTypes(HttpService:JSONDecode(json))
end

return JsonCrypto
