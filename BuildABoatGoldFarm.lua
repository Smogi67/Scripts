--!nocheck
-- ============================================================
--  BUILD A BOAT SCRIPT  —  Gold Farm
--  UI: LiquidGlass (MacUiCoreLib)
-- ============================================================
--  Toggle "Gold farm" to tween through the 4 waypoints, touch
--  workspace.BoatStages.NormalStages.TheEnd.GoldenChest, wait
--  for the reset, then start the route over on respawn.
-- ============================================================

-- Clear executor HTTP cache so the library always loads fresh
pcall(function() if clear_cache then clear_cache() end end)
pcall(function() if clearcache then clearcache() end end)
pcall(function() if syn and syn.clear_cache then syn.clear_cache() end end)

local LiquidGlass = loadstring(game:HttpGet(
	"https://raw.githubusercontent.com/Smogi67/MacUiCoreLib/refs/heads/main/CoreLibraryElements.lua?v=" .. tick()
))()

-- ── Services ─────────────────────────────────────────────────
local Players      = game:GetService("Players")
local TweenService = game:GetService("TweenService")
local RunService   = game:GetService("RunService")

local LocalPlayer = Players.LocalPlayer

-- ── Route config ─────────────────────────────────────────────
local WAYPOINTS = {
	Vector3.new(-47.2,  51.9, 1301.7),
	Vector3.new(-48.0,  17.5, 8613.9),
	Vector3.new(-51.3,   1.4, 8745.6),
	Vector3.new(-55.50651550292969, -362.089599609375, 9495.9560546875),
}

local CHEST_PATH = { "BoatStages", "NormalStages", "TheEnd", "GoldenChest" }

-- The two containers that hold every stage. Each direct child of these
-- is treated as one "stage" (e.g. BoatStages.NormalStages.Stage3,
-- BoatStages.OtherStages.SecretRoom, ...).
local STAGE_GROUPS = {
	{ folder = "NormalStages", label = "Normal" },
	{ folder = "OtherStages",  label = "Other"  },
}
local STAGE_POLL_INTERVAL = 0.25 -- how often the Stage row refreshes

-- ── Stage confirmer ──────────────────────────────────────────
-- Each stage carries a big dark "wall" part that registers your progress.
-- With the confirmer on, the farm stops inside every wall it passes through,
-- spins the character in a fast horizontal + vertical circle so the touch
-- definitely lands, then resumes the leg at whatever the slider is set to.
local WALL_NAME_HINTS = { "wall", "stage", "checkpoint", "check", "trigger", "detect", "zone", "region" }
local WALL_MIN_FACE   = 40    -- studs: both large sides must exceed this
local WALL_MAX_THICK  = 25    -- studs: the thin side must stay under this
local WALL_MAX_BRIGHT = 0.22  -- 0-1: how dark the part has to be to count as black
local WALL_PADDING    = 2     -- studs of slack around the wall box
local WIGGLE_RADIUS   = 3     -- studs of the circle
local WIGGLE_REVS     = 5     -- revolutions per axis
local WIGGLE_RATE     = 14    -- revolutions per second

local MIN_SPEED     = 50    -- studs/sec at slider 0%
local MAX_SPEED     = 1200  -- studs/sec at slider 100%
local RESET_TIMEOUT = 15    -- how long to wait for the chest to reset us
local SPAWN_TIMEOUT = 30    -- how long to wait for the new character
local SETTLE_TIME   = 1.0   -- pause after respawn before tweening again

-- ── State ────────────────────────────────────────────────────
local farming      = false
local runToken     = 0      -- invalidates old loops when toggled off/on
local speedAlpha   = 0.35
local laps         = 0
local confirmWalls = false

local farmToggle, statusInfo, lapInfo, speedInfo, stageInfo, wallInfo

local function currentSpeed()
	return MIN_SPEED + (MAX_SPEED - MIN_SPEED) * speedAlpha
end

local function setStatus(text)
	if statusInfo then pcall(function() statusInfo:SetValue(text) end) end
end

-- ── Stage detection ──────────────────────────────────────────
-- Every direct child of BoatStages.NormalStages / BoatStages.OtherStages is
-- indexed with its oriented bounding box. The stage we are "at" is the
-- smallest box the HumanoidRootPart sits inside; if we are between stages
-- (mid-tween, or down at the chest), the nearest box is shown instead.
local stageIndex      = {}
local stageCount      = 0
local lastStageText   = nil
local rebuildQueued   = false
local wallIndex       = {}   -- { part = BasePart, stage = "Normal / Stage3" }
local wallCount       = 0
local confirmedWalls  = {}   -- parts already confirmed this lap

local function boundsOf(instance)
	if instance:IsA("BasePart") then
		return instance.CFrame, instance.Size
	end

	if instance:IsA("Model") then
		local ok, cf, size = pcall(function() return instance:GetBoundingBox() end)
		if ok and cf and size and size.Magnitude > 0 then
			return cf, size
		end
	end

	-- Folders / models GetBoundingBox choked on: build an AABB from descendants
	local min, max
	for _, d in ipairs(instance:GetDescendants()) do
		if d:IsA("BasePart") then
			local half = d.Size * 0.5
			local lo, hi = d.Position - half, d.Position + half
			if min then
				min = Vector3.new(math.min(min.X, lo.X), math.min(min.Y, lo.Y), math.min(min.Z, lo.Z))
				max = Vector3.new(math.max(max.X, hi.X), math.max(max.Y, hi.Y), math.max(max.Z, hi.Z))
			else
				min, max = lo, hi
			end
		end
	end
	if min then
		return CFrame.new((min + max) * 0.5), (max - min) + Vector3.new(4, 4, 4)
	end
	return nil
end

-- A stage wall: large flat slab, and either near-black or named like a trigger.
local function isWallPart(inst)
	if not inst:IsA("BasePart") then return false end

	local dims = { inst.Size.X, inst.Size.Y, inst.Size.Z }
	table.sort(dims)
	if dims[1] > WALL_MAX_THICK then return false end
	if dims[2] < WALL_MIN_FACE or dims[3] < WALL_MIN_FACE then return false end

	local c = inst.Color
	if (c.R + c.G + c.B) / 3 <= WALL_MAX_BRIGHT then return true end

	local lower = inst.Name:lower()
	for _, hint in ipairs(WALL_NAME_HINTS) do
		if string.find(lower, hint, 1, true) then return true end
	end
	return false
end

local function buildStageIndex()
	local index = {}
	local walls = {}
	local boatStages = workspace:FindFirstChild("BoatStages")

	if boatStages then
		for _, group in ipairs(STAGE_GROUPS) do
			local folder = boatStages:FindFirstChild(group.folder)
			if folder then
				for _, stage in ipairs(folder:GetChildren()) do
					local label = group.label .. " / " .. stage.Name

					local cf, size = boundsOf(stage)
					if cf then
						table.insert(index, {
							label  = label,
							cf     = cf,
							half   = size * 0.5,
							volume = size.X * size.Y * size.Z,
						})
					end

					if isWallPart(stage) then
						table.insert(walls, { part = stage, stage = label })
					end
					for _, d in ipairs(stage:GetDescendants()) do
						if isWallPart(d) then
							table.insert(walls, { part = d, stage = label })
						end
					end
				end
			end
		end
	end

	stageIndex = index
	stageCount = #index
	wallIndex  = walls
	wallCount  = #walls

	if wallInfo then pcall(function() wallInfo:SetValue(tostring(wallCount)) end) end
	return stageCount, wallCount
end

-- Returns: label, inside (bool), distanceToBox
local function stageAt(position)
	if stageCount == 0 then return nil, false, 0 end

	local inside, insideVolume
	local nearest, nearestDist

	for _, s in ipairs(stageIndex) do
		local rel = s.cf:PointToObjectSpace(position)
		local dx  = math.max(math.abs(rel.X) - s.half.X, 0)
		local dy  = math.max(math.abs(rel.Y) - s.half.Y, 0)
		local dz  = math.max(math.abs(rel.Z) - s.half.Z, 0)
		local gap = math.sqrt(dx * dx + dy * dy + dz * dz) -- 0 when inside the box

		if gap == 0 then
			-- overlapping stages: the tighter box is the more specific answer
			if not insideVolume or s.volume < insideVolume then
				inside, insideVolume = s, s.volume
			end
		elseif not nearestDist or gap < nearestDist then
			nearest, nearestDist = s, gap
		end
	end

	if inside  then return inside.label, true, 0 end
	if nearest then return nearest.label, false, nearestDist end
	return nil, false, 0
end

local function updateStageDisplay(position)
	if not stageInfo then return end

	local text
	if stageCount == 0 then
		text = "no stages found"
	else
		local label, isInside, dist = stageAt(position)
		if not label then
			text = "—"
		elseif isInside then
			text = label
		else
			text = ("near %s (%d)"):format(label, math.round(dist))
		end
	end

	if text ~= lastStageText then
		lastStageText = text
		pcall(function() stageInfo:SetValue(text) end)
	end
end

-- Stages stream in and out, so re-index when the folders change (debounced)
local function queueRebuild()
	if rebuildQueued then return end
	rebuildQueued = true
	task.delay(1, function()
		rebuildQueued = false
		buildStageIndex()
		lastStageText = nil
	end)
end

local function hookStageFolders()
	local boatStages = workspace:FindFirstChild("BoatStages")
	if not boatStages then return end
	for _, group in ipairs(STAGE_GROUPS) do
		local folder = boatStages:FindFirstChild(group.folder)
		if folder then
			folder.ChildAdded:Connect(queueRebuild)
			folder.ChildRemoved:Connect(queueRebuild)
		end
	end
end

-- ── Character helpers ────────────────────────────────────────
local function getParts()
	local char = LocalPlayer.Character
	if not char or not char.Parent then return nil end
	local hrp = char:FindFirstChild("HumanoidRootPart")
	local hum = char:FindFirstChildOfClass("Humanoid")
	if not hrp or not hum then return nil end
	return char, hrp, hum
end

-- Waits for a living character. Returns nil if the farm was stopped.
local function waitForCharacter(token, timeout)
	local t0 = os.clock()
	while farming and runToken == token do
		local char, hrp, hum = getParts()
		if char and hum.Health > 0 then
			return char, hrp, hum
		end
		if timeout and os.clock() - t0 > timeout then return nil end
		task.wait(0.1)
	end
	return nil
end

-- ── Chest helpers ────────────────────────────────────────────
local function resolveChest()
	local node = workspace
	for _, name in ipairs(CHEST_PATH) do
		node = node:FindFirstChild(name)
		if not node then return nil end
	end
	if node:IsA("BasePart") then return node end
	if node:IsA("Model") then
		return node.PrimaryPart or node:FindFirstChildWhichIsA("BasePart", true)
	end
	return nil
end

local fireTouch = (typeof(firetouchinterest) == "function" and firetouchinterest)
	or (typeof(fireTouchInterest) == "function" and fireTouchInterest)
	or nil

-- Physical contact usually fires on its own; firetouchinterest is a backup.
local function touchChest(hrp)
	local chest = resolveChest()
	if not chest then
		LiquidGlass:NotifyError("Chest not found", "Path changed?")
		return false
	end
	if fireTouch then
		for _ = 1, 3 do
			pcall(fireTouch, hrp, chest, 0)
			task.wait(0.05)
			pcall(fireTouch, hrp, chest, 1)
			task.wait(0.05)
		end
	end
	return true
end

-- ── Stage confirmer ─────────────────────────────────────
local function wallContaining(position)
	for _, w in ipairs(wallIndex) do
		local part = w.part
		if part.Parent then
			local rel  = part.CFrame:PointToObjectSpace(position)
			local half = part.Size * 0.5
			if  math.abs(rel.X) <= half.X + WALL_PADDING
			and math.abs(rel.Y) <= half.Y + WALL_PADDING
			and math.abs(rel.Z) <= half.Z + WALL_PADDING then
				return w
			end
		end
	end
	return nil
end

-- At high speeds one frame can skip clean through a thin wall, so test a few
-- points along the segment we travelled since the last frame, not just the end.
local function wallOnSegment(from, to)
	local hit = wallContaining(to)
	if hit then return hit end

	local dist = (to - from).Magnitude
	if dist < 4 then return nil end

	local steps = math.clamp(math.ceil(dist / 4), 1, 32)
	for i = 1, steps - 1 do
		hit = wallContaining(from:Lerp(to, i / steps))
		if hit then return hit end
	end
	return nil
end

-- Fast circle inside the wall: one horizontal loop, then one vertical loop.
local function confirmWiggle(hrp, hum, wall, token)
	local base     = hrp.CFrame
	local duration = WIGGLE_REVS / WIGGLE_RATE

	local function spin(offsetFor)
		local t0 = os.clock()
		while true do
			local elapsed = os.clock() - t0
			if elapsed >= duration then break end
			if not farming or runToken ~= token or not hrp.Parent or hum.Health <= 0 then
				return false
			end
			local angle = elapsed * WIGGLE_RATE * math.pi * 2
			hrp.CFrame = base * CFrame.new(offsetFor(angle))
			hrp.AssemblyLinearVelocity  = Vector3.zero
			hrp.AssemblyAngularVelocity = Vector3.zero
			RunService.Heartbeat:Wait()
		end
		return true
	end

	local ok = spin(function(a)
		return Vector3.new(math.cos(a) * WIGGLE_RADIUS, 0, math.sin(a) * WIGGLE_RADIUS)
	end)

	if ok then
		ok = spin(function(a)
			return Vector3.new(math.cos(a) * WIGGLE_RADIUS, math.sin(a) * WIGGLE_RADIUS, 0)
		end)
	end

	if ok then
		hrp.CFrame = base
		hrp.AssemblyLinearVelocity = Vector3.zero
	end

	-- belt and braces: poke the wall's touch interest directly too
	if fireTouch and wall and wall.part and wall.part.Parent then
		pcall(fireTouch, hrp, wall.part, 0)
		task.wait(0.03)
		pcall(fireTouch, hrp, wall.part, 1)
	end

	return ok
end

-- ── Tweening ─────────────────────────────────────────────────
-- Returns true only if the leg finished cleanly.
local function tweenTo(hrp, hum, target, token)
	-- Loops: each pass tweens toward the target until we either arrive or hit
	-- an unconfirmed stage wall. After a wall the remaining distance is
	-- re-tweened at the current slider speed.
	while true do
		local distance = (hrp.Position - target).Magnitude
		local duration = math.max(distance / currentSpeed(), 0.05)

		local tween = TweenService:Create(
			hrp,
			TweenInfo.new(duration, Enum.EasingStyle.Linear, Enum.EasingDirection.InOut),
			{ CFrame = CFrame.new(target) }
		)

		local finished = false
		local conn = tween.Completed:Connect(function() finished = true end)
		local lastPos = hrp.Position
		local hitWall = nil

		tween:Play()

		while not finished do
			if not farming or runToken ~= token or not hrp.Parent or hum.Health <= 0 then
				tween:Cancel()
				conn:Disconnect()
				return false
			end

			-- keep physics from flinging us mid-tween
			hrp.AssemblyLinearVelocity  = Vector3.zero
			hrp.AssemblyAngularVelocity = Vector3.zero

			if confirmWalls and wallCount > 0 then
				local pos = hrp.Position
				local w = wallOnSegment(lastPos, pos)
				lastPos = pos
				if w and not confirmedWalls[w.part] then
					hitWall = w
					break
				end
			end

			RunService.Heartbeat:Wait()
		end

		conn:Disconnect()

		if not hitWall then
			hrp.AssemblyLinearVelocity = Vector3.zero
			return true
		end

		tween:Cancel()
		confirmedWalls[hitWall.part] = true
		setStatus("Confirming " .. hitWall.stage)

		if not confirmWiggle(hrp, hum, hitWall, token) then
			return false
		end
		-- fall through: re-tween the rest of the leg at the slider speed
	end
end

-- ── Main farm loop ───────────────────────────────────────────
local function runFarm(token)
	while farming and runToken == token do
		local char, hrp, hum = waitForCharacter(token, SPAWN_TIMEOUT)
		if not char then break end

		-- get out of any seat first, otherwise the weld drags us back
		if hum.SeatPart then
			hum.Sit = false
			task.wait(0.2)
			char, hrp, hum = getParts()
			if not hrp then break end
		end

		confirmedWalls = {}

		local completed = true
		for i, point in ipairs(WAYPOINTS) do
			setStatus(("Waypoint %d/%d"):format(i, #WAYPOINTS))
			if not tweenTo(hrp, hum, point, token) then
				completed = false
				break
			end
		end

		if not (farming and runToken == token) then break end

		if completed then
			setStatus("At chest")
			LiquidGlass:Notification({
				title   = "Golden Chest reached",
				message = ("Lap %d — waiting for the reset."):format(laps + 1),
			})
			touchChest(hrp)

			-- wait for the chest to reset us
			local wasReset = false
			local t0 = os.clock()
			while farming and runToken == token do
				if hum.Health <= 0 or not char.Parent or LocalPlayer.Character ~= char then
					wasReset = true
					break
				end
				if os.clock() - t0 > RESET_TIMEOUT then break end
				task.wait(0.1)
			end

			if not (farming and runToken == token) then break end

			if wasReset then
				setStatus("Respawning")
				if not waitForCharacter(token, SPAWN_TIMEOUT) then break end
				task.wait(SETTLE_TIME)

				laps += 1
				if lapInfo then pcall(function() lapInfo:SetValue(tostring(laps)) end) end

				LiquidGlass:Notification({
					title   = "Restarting farm",
					message = ("Respawned — starting lap %d."):format(laps + 1),
				})
			else
				LiquidGlass:NotifyWarning("No reset detected", "Running the route again")
				task.wait(1)
			end
		else
			-- died mid-route or the toggle went off
			if farming and runToken == token then
				setStatus("Interrupted")
				task.wait(1)
			end
		end
	end

	if runToken == token then
		setStatus("Idle")
	end
end

-- ── Start / stop ─────────────────────────────────────────────
local function startFarm()
	if farming then return end
	farming  = true
	runToken += 1
	local token = runToken

	buildStageIndex()
	lastStageText = nil

	setStatus("Starting")
	LiquidGlass:Notify("Gold farm", "Enabled")

	task.spawn(function()
		runFarm(token)
	end)
end

local function stopFarm()
	if not farming then return end
	farming  = false
	runToken += 1
	setStatus("Idle")
	LiquidGlass:Notify("Gold farm", "Disabled")
end

-- ============================================================
--  UI
-- ============================================================
LiquidGlass:SetConfig({
	title = "Build a Boat Script",
})

local farmTab = LiquidGlass:AddTab("Farm", nil, "Gold farm")

-- ── Farm section ─────────────────────────────────────────────
local farmSec = farmTab:AddSection("Gold Farm")

farmSec:AddLabel("Tweens through 4 waypoints to the Golden Chest, waits for the reset, then repeats on respawn.")

farmToggle = farmSec:AddToggle("Gold farm", false, function(on)
	if on then startFarm() else stopFarm() end
end)

farmSec:AddToggle("Stage confirmer", false, function(on)
	confirmWalls = on
	if on then
		LiquidGlass:Notify("Stage confirmer", wallCount .. " wall" .. (wallCount == 1 and "" or "s") .. " tracked")
	else
		LiquidGlass:Notify("Stage confirmer", "Off")
	end
end)

farmSec:AddLabel("Confirmer: stops inside each stage wall, spins fast in a horizontal then vertical circle, then carries on at the slider speed.")

farmSec:AddSlider("Tween speed", speedAlpha, function(v)
	speedAlpha = v
	local s = math.round(currentSpeed())
	if speedInfo then pcall(function() speedInfo:SetValue(s .. " studs/s") end) end
	LiquidGlass:Notify("Tween speed", s .. " studs/s", "slider")
end)

-- ── Status section ───────────────────────────────────────────
local statSec = farmTab:AddSection("Status")

statusInfo = statSec:AddInfo("State", "Idle")
stageInfo  = statSec:AddInfo("Stage", "—")
wallInfo   = statSec:AddInfo("Stage walls", "0")
lapInfo    = statSec:AddInfo("Laps",  "0")
speedInfo  = statSec:AddInfo("Speed", math.round(currentSpeed()) .. " studs/s")

statSec:AddButton("Rescan stages", "Scan", function()
	local found, walls = buildStageIndex()
	lastStageText = nil
	confirmedWalls = {}
	local _, hrp = getParts()
	if hrp then updateStageDisplay(hrp.Position) end
	LiquidGlass:Notify("Stage index", found .. " stages, " .. walls .. " walls")
end)

-- If the confirmer misses walls, this prints what it did find to the console
statSec:AddButton("Print wall parts", "Print", function()
	print(("[BAB] %d stage walls indexed"):format(wallCount))
	for i, w in ipairs(wallIndex) do
		local p = w.part
		print(("[BAB] %d. %s | %s | size %s | colour %s")
			:format(i, w.stage, p.Name, tostring(p.Size), tostring(p.Color)))
	end
	LiquidGlass:Notify("Wall parts", wallCount .. " printed to console")
end)

statSec:AddButton("Reset lap counter", "Reset", function()
	laps = 0
	if lapInfo then pcall(function() lapInfo:SetValue("0") end) end
	LiquidGlass:Notify("Lap counter", "Reset to 0")
end)

-- Keep the toggle honest if the character disappears entirely
LocalPlayer.CharacterRemoving:Connect(function()
	if farming then setStatus("Respawning") end
end)

-- ── Live stage tracking ──────────────────────────────────────
-- Index the stages once BoatStages exists, then keep the Stage row updated
-- whether the farm is running or not.
task.spawn(function()
	local boatStages = workspace:FindFirstChild("BoatStages")
	local waited = 0
	while not boatStages and waited < 30 do
		task.wait(0.5)
		waited += 0.5
		boatStages = workspace:FindFirstChild("BoatStages")
	end

	local found = buildStageIndex()
	hookStageFolders()

	if found == 0 then
		LiquidGlass:NotifyWarning("No stages found", "Check BoatStages path")
	end

	while true do
		local _, hrp = getParts()
		if hrp then updateStageDisplay(hrp.Position) end
		task.wait(STAGE_POLL_INTERVAL)
	end
end)

LiquidGlass:Notification({
	title   = "Build a Boat Script",
	message = "Loaded. Flip the toggle to start farming.",
})
