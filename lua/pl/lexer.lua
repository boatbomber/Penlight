--- Lexical scanner for creating a sequence of tokens from text.
-- `lexer.scan(s)` returns an iterator over all tokens found in the
-- string `s`. This iterator returns two values, a token type string
-- (such as 'string' for quoted string, 'iden' for identifier) and the value of the
-- token.
--
-- Versions specialized for Lua and C are available; these also handle block comments
-- and classify keywords as 'keyword' tokens. For example:
--
--    > s = "for i=1,n do"
--    > for t,v in lexer.lua(s)  do print(t,v) end
--    keyword for
--    iden    i
--    =       =
--    number  1
--    ,       ,
--    iden    n
--    keyword do
--
-- See the Guide for further @{06-data.md.Lexical_Scanning|discussion}
-- @module pl.lexer

local yield, wrap = coroutine.yield, coroutine.wrap
local strfind = string.find
local strsub = string.sub
local append = table.insert

local function assert_arg(idx, val, tp)
	if (type(val) ~= tp) then
		error("argument " .. idx .. " must be " .. tp, 2)
	end
end

local lexer = {}

local NUMBER1	= "^[%+%-]?%d+%.?%d*[eE][%+%-]?%d+"
local NUMBER2	= "^[%+%-]?%d+%.?%d*"
local NUMBER3	= "^0x[%da-fA-F]+"
local NUMBER4	= "^%d+%.?%d*[eE][%+%-]?%d+"
local NUMBER5	= "^%d+%.?%d*"
local IDEN		= "^[%a_][%w_]*"
local WSPACE	= "^%s+"
local STRING1	= "^(['\"])%1"							--Empty String
local STRING2	= [[^(['"])(\*)%2%1]]
local STRING3	= [[^(['"]).-[^\](\*)%2%1]]
local STRING4	= "^(['\"]).-.*"						--Incompleted String
local STRING5	= "^%[(=*)%[.-%]%1%]"					--Multiline-String
local STRING6	= "^%[%[.-.*"							--Incompleted Multiline-String
local CHAR1		= "^''"
local CHAR2		= [[^'(\*)%1']]
local CHAR3		= [[^'.-[^\](\*)%1']]
local PREPRO	= "^#.-[^\\]\n"
local MCOMMENT1	= "^%-%-%[(=*)%[.-%]%1%]"				--Completed Multiline-Comment
local MCOMMENT2	= "^%-%-%[%[.-.*"						--Incompleted Multiline-Comment
local SCOMMENT1	= "^%-%-.-\n"							--Completed Singleline-Comment
local SCOMMENT2	= "^%-%-.-.*"							--Incompleted Singleline-Comment


local plain_matches, lua_matches, lua_keyword, lua_builtin

local function tdump(tok)
	return yield(tok,tok)
end

local function ndump(tok, options)
	return yield("number", tok)
end

-- regular strings, single or double quotes; usually we want them
-- without the quotes
local function sdump(tok, options)
	return yield("string", tok)
end

local function chdump(tok, options)
	return yield("char", tok)
end

local function cdump(tok)
	return yield("comment", tok)
end

local function wsdump(tok)
	return yield("space", tok)
end

local function pdump(tok)
	return yield("prepro", tok)
end

local function plain_vdump(tok)
	return yield("iden", tok)
end

local function lua_vdump(tok)
	if (lua_keyword[tok]) then
		return yield("keyword", tok)
	elseif (lua_builtin[tok]) then
		return yield("builtin", tok)
	else
		return yield("iden", tok)
	end
end


--- create a plain token iterator from a string or file-like object.
-- @tparam string|file s a string or a file-like object with `:read()` method returning lines.
-- @tab matches an optional match table - array of token descriptions.
-- A token is described by a `{pattern, action}` pair, where `pattern` should match
-- token body and `action` is a function called when a token of described type is found.
-- @tab[opt] filter a table of token types to exclude, by default `{space=true}`
-- @tab[opt] options a table of options; by default, `{number=true,string=true}`,
-- which means convert numbers and strip string quotes.
function lexer.scan(s, matches, filter, options)
	local file = (type(s) ~= "string" and s)
	filter = (filter or {space = true})
	options = (options or {number = true, string = true})
	if (filter) then
		if (filter.space) then
			filter[wsdump] = true
		end
		if (filter.comments) then
			filter[cdump] = true
		end
	end
	if (not matches) then
		if (not plain_matches) then
			plain_matches = {
				{WSPACE, wsdump},
				{NUMBER3, ndump},
				{IDEN, plain_vdump},
				{NUMBER1, ndump},
				{NUMBER2, ndump},
				{STRING1, sdump},
				{STRING2, sdump},
				{STRING3, sdump},
				{"^.", tdump}
			}
		end
		matches = plain_matches
	end
	local function lex(first_arg)
		local line_nr = 0
		local next_line = (file and file:read())
		local sz = (file and 0 or #s)
		local idx = 1

		-- res is the value used to resume the coroutine.
		local function handle_requests(res)
			while (res) do
				local tp = type(res)
				-- insert a token list
				if (tp == "table") then
					res = yield("", "")
					for _,t in ipairs(res) do
						res = yield(t[1], t[2])
					end
				elseif (tp == "string") then -- or search up to some special pattern
					local i1, i2 = strfind(s, res, idx)
					if (i1) then
						local tok = strsub(s, i1, i2)
						idx = (i2 + 1)
						res = yield("", tok)
					else
						res = yield("", "")
						idx = (sz + 1)
					end
				else
					res = yield(line_nr, idx)
				end
			end
		end

		handle_requests(first_arg)
		if (not file) then
			line_nr = 1
		end

		while (true) do
			if (idx > sz) then
				if (file) then
					if (not next_line) then return end
					s = next_line
					line_nr = (line_nr + 1)
					next_line = file:read()
					if next_line then
						s = (s .. "\n")
					end
					idx, sz = 1, #s
				else
					while (true) do
						handle_requests(yield())
					end
				end
			end

			for _,m in ipairs(matches) do
				local pat = m[1]
				local fun = m[2]
				local findres = {strfind(s, pat, idx)}
				local i1, i2 = findres[1], findres[2]
				if (i1) then
					local tok = strsub(s, i1, i2)
					idx = (i2 + 1)
					local res
					if (not (filter and filter[fun])) then
						lexer.finished = (idx > sz)
						res = fun(tok, options, findres)
					end
					if (not file and tok:find("\n")) then
						-- Update line number.
						local _, newlines = tok:gsub("\n", {})
						line_nr = (line_nr + newlines)
					end
					handle_requests(res)
					break
				end
			end
		end
	end
	return wrap(lex)
end

local function isstring(s)
	return (type(s) == "string")
end

--- insert tokens into a stream.
-- @param tok a token stream
-- @param a1 a string is the type, a table is a token list and
-- a function is assumed to be a token-like iterator (returns type & value)
-- @string a2 a string is the value
function lexer.insert(tok, a1, a2)
	if (not a1) then return end
	local ts
	if (isstring(a1) and isstring(a2)) then
		ts = {{a1,a2}}
	elseif (type(a1) == "function") then
		ts = {}
		for t,v in a1() do
			append(ts, {t, v})
		end
	else
		ts = a1
	end
	tok(ts)
end

--- get everything in a stream upto a newline.
-- @param tok a token stream
-- @return a string
function lexer.getline(tok)
	local _,v = tok(".-\n")
	return v
end

--- get current line number.
-- @param tok a token stream
-- @return the line number.
-- if the input source is a file-like object,
-- also return the column.
function lexer.lineno(tok)
	return tok(0)
end

--- get the rest of the stream.
-- @param tok a token stream
-- @return a string
function lexer.getrest(tok)
	local _,v = tok(".+")
	return v
end

--- get the Lua keywords as a set-like table.
-- So `res["and"]` etc would be `true`.
-- @return a table
function lexer.get_keywords()
	if (not lua_keyword) then
		lua_keyword = {
			["and"] = true,	["break"] = true,	["do"] = true,		["else"] = true,		["elseif"] = true,
			["end"] = true,	["false"] = true,	["for"] = true,		["function"] = true,	["if"] = true,
			["in"] = true,	["local"] = true,	["nil"] = true,		["not"] = true,			["while"] = true,
			["or"] = true,	["repeat"] = true,	["return"] = true,	["then"] = true,		["true"] = true,
			["until"] = true
		}
	end
	return lua_keyword
end
		
--- get the Lua built-in functionss as a set-like table.
-- So `res["print"]` etc would be `true`.
-- @return a table
--Note: Commented out sections are builtins that would normally be highlighted, but because they have an operator in the middle
--		they screw things up so it's not worth trying to fix. I left them here in case someone else wants to add them in
function lexer.get_builtins()
	if (not lua_builtin) then
		lua_builtin = {
			['assert'] = true;['collectgarbage'] = true;['error'] = true;['_G'] = true;
			['gcinfo'] = true;['getfenv'] = true;['getmetatable'] = true;['ipairs'] = true;
			['loadstring'] = true;['newproxy'] = true;['next'] = true;['pairs'] = true;
			['pcall'] = true;['print'] = true;['rawequal'] = true;['rawget'] = true;['rawset'] = true;
			['select'] = true;['setfenv'] = true;['setmetatable'] = true;['tonumber'] = true;
			['tostring'] = true;['type'] = true;['unpack'] = true;['_VERSION'] = true;['xpcall'] = true;
			['delay'] = true;['elapsedTime'] = true;['require'] = true;['spawn'] = true;['tick'] = true;
			['time'] = true;['typeof'] = true;['UserSettings'] = true;['wait'] = true;['warn'] = true;
			['game'] = true;['Enum'] = true;['script'] = true;['shared'] = true;['workspace'] = true;
			['Axes'] = true;['BrickColor'] = true;['CFrame'] = true;['Color3'] = true;['ColorSequence'] = true;
			['ColorSequenceKeypoint'] = true;['Faces'] = true;['Instance'] = true;['NumberRange'] = true;
			['NumberSequence'] = true;['NumberSequenceKeypoint'] = true;['PhysicalProperties'] = true;
			['Random'] = true;['Ray'] = true;['Rect'] = true;['Region3'] = true;['Region3int16'] = true;
			['TweenInfo'] = true;['UDim'] = true;['UDim2'] = true;['Vector2'] = true;['Vector3'] = true;
			['Vector3int16'] = true;['next'] = true;
			['os'] = true;
			--['os.time'] = true;['os.date'] = true;['os.difftime'] = true;
			['debug'] = true;
			--['debug.traceback'] = true;['debug.profilebegin'] = true;['debug.profileend'] = true;
			['math'] = true;
			--['math.abs'] = true;['math.acos'] = true;['math.asin'] = true;['math.atan'] = true;['math.atan2'] = true;['math.ceil'] = true;['math.clamp'] = true;['math.cos'] = true;['math.cosh'] = true;['math.deg'] = true;['math.exp'] = true;['math.floor'] = true;['math.fmod'] = true;['math.frexp'] = true;['math.ldexp'] = true;['math.log'] = true;['math.log10'] = true;['math.max'] = true;['math.min'] = true;['math.modf'] = true;['math.noise'] = true;['math.pow'] = true;['math.rad'] = true;['math.random'] = true;['math.randomseed'] = true;['math.sign'] = true;['math.sin'] = true;['math.sinh'] = true;['math.sqrt'] = true;['math.tan'] = true;['math.tanh'] = true;
			['coroutine'] = true;
			--['coroutine.create'] = true;['coroutine.resume'] = true;['coroutine.running'] = true;['coroutine.status'] = true;['coroutine.wrap'] = true;['coroutine.yield'] = true;
			['string'] = true;
			--['string.byte'] = true;['string.char'] = true;['string.dump'] = true;['string.find'] = true;['string.format'] = true;['string.len'] = true;['string.lower'] = true;['string.match'] = true;['string.rep'] = true;['string.reverse'] = true;['string.sub'] = true;['string.upper'] = true;['string.gmatch'] = true;['string.gsub'] = true;
			['table'] = true;
			--['table.concat'] = true;['table.insert'] = true;['table.remove'] = true;['table.sort'] = true;
		}
	end
	return lua_builtin
end

--- create a Lua token iterator from a string or file-like object.
-- Will return the token type and value.
-- @string s the string
-- @tab[opt] filter a table of token types to exclude, by default `{space=true,comments=true}`
-- @tab[opt] options a table of options; by default, `{number=true,string=true}`,
-- which means convert numbers and strip string quotes.

function lexer.lua(s, filter, options)
	filter = (filter or {space = true, comments = true})
	lexer.get_keywords()
	lexer.get_builtins()

	if (not lua_matches) then
		lua_matches = {
			{IDEN,		lua_vdump},			-- Indentifiers
			{WSPACE,	wsdump},			-- Whitespace
			{NUMBER3,	ndump},				-- Numbers
			{NUMBER4,	ndump},
			{NUMBER5,	ndump},
			{STRING1,	sdump},				-- Strings
			{STRING2,	sdump},
			{STRING3,	sdump},
			{STRING4,	sdump},
			{STRING5,	sdump},				-- Multiline-Strings
			{STRING6,	sdump},				-- Multiline-Strings
			
			{MCOMMENT1,	cdump},				-- Multiline-Comments
			{MCOMMENT2,	cdump},			
			{SCOMMENT1,	cdump},				-- Singleline-Comments
			{SCOMMENT2,	cdump},
			
			{"^==",		tdump},				-- Operators
			{"^~=",		tdump},
			{"^<=",		tdump},
			{"^>=",		tdump},
			{"^%.%.%.",	tdump},
			{"^%.%.",	tdump},
			{"^.",		tdump}
		}
	end
	return lexer.scan(s, lua_matches, filter, options)
end

--- get a list of parameters separated by a delimiter from a stream.
-- @param tok the token stream
-- @string[opt=')'] endtoken end of list. Can be '\n'
-- @string[opt=','] delim separator
-- @return a list of token lists.
function lexer.get_separated_list(tok, endtoken, delim)
	endtoken = (endtoken or ")")
	delim = (delim or ",")
	local parm_values = {}
	local level = 1 -- used to count ( and )
	local tl = {}
	local function tappend(tl, t, val)
		val = (val or t)
		append(tl, {t, val})
	end
	local is_end
	if (endtoken == "\n") then
		is_end = function(t,val)
			return (t == "space" and val:find("\n"))
		end
	else
		is_end = function (t)
			return (t == endtoken)
		end
	end
	local token, value
	while (true) do
		token, value = tok()
		if (not token) then return nil, "EOS" end -- end of stream is an error!
		if (is_end(token, value) and level == 1) then
			append(parm_values, tl)
			break
		elseif (token == "(") then
			level = (level + 1)
			tappend(tl, "(")
		elseif (token == ")") then
			level = (level - 1)
			if (level == 0) then -- finished with parm list
				append(parm_values, tl)
				break
			else
				tappend(tl, ")")
			end
		elseif (token == delim and level == 1) then
			append(parm_values, tl) -- a new parm
			tl = {}
		else
			tappend(tl, token, value)
		end
	end
	return parm_values, {token, value}
end

--- get the next non-space token from the stream.
-- @param tok the token stream.
function lexer.skipws(tok)
	local t,v = tok()
	while (t == "space") do
		t,v = tok()
	end
	return t,v
end

local skipws = lexer.skipws

--- get the next token, which must be of the expected type.
-- Throws an error if this type does not match!
-- @param tok the token stream
-- @string expected_type the token type
-- @bool no_skip_ws whether we should skip whitespace
function lexer.expecting(tok, expected_type, no_skip_ws)
	assert_arg(1, tok, "function")
	assert_arg(2, expected_type, "string")
	local t,v
	if (no_skip_ws) then
		t,v = tok()
	else
		t,v = skipws(tok)
	end
	if (t ~= expected_type) then error("expecting " .. expected_type, 2) end
	return v
end

return lexer
